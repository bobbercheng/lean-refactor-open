#!/usr/bin/env python3
"""The open-track warm-up 15 upload candidate from the from-seed A100 lineage (p85 + its continuation p85b; operator 2026-10-31 07:15 UTC:
"Yes, upload at >= 85"), and its OFFICIAL-matching measurement. The coordinator uploads; this only prepares and measures.

  pick     (no Lean, seconds) per warm-up row, the highest STORED score among every from-seed candidate of the lineage:
             the runs' exports (OUT/proofs.jsonl: end / normalize / agent / seed) and their banked agent bests (OUT/work/<row>/state.json);
           a candidate must start with the row's exact statement + `:=` (scorer.tokenize.split_declaration) and pass the forbidden-pattern
           check (scorer.forbidden: the Space's list); writes <dir>/candidate.jsonl ({name, proof}, warm-up order) + <dir>/pick.json.
  measure  (Lean; ONLY inside a memory-capped unit) every picked proof through probe/calib/eval_official.py --all-pins (the direct-path meter,
           the worker's `:=`+newline token rule and the h * R_off / R_direct + 2 heartbeat prediction: the meter that predicted sub13 83.37
           against the worker's 83.31); with --alternates also the runner-up of every row whose top two stored scores are within 0.3 (the
           stored scores come from different meters: normalize understates by up to 0.3), and the pick is re-made on the measured score;
           writes <dir>/pred.json (submit/candidates/*.pred.json format), <dir>/candidate.jsonl (re-picked), <dir>/measure.jsonl and prints
           the predicted warm-up mean and GO (>= --target, default 85) / NO-GO.

    python3 probe/a100/warmup_upload_measure.py pick --runs probe/a100-reh-p85/out probe/a100-reh-p85b/out --dir probe/a100-upload/p85b
    systemd-run --user --wait --collect -u lra-upload-measure -p MemoryMax=48G -p OOMPolicy=continue -p CPUWeight=50 -p RuntimeMaxSec=7200 \\
      --working-directory=$PWD -E PATH -E HOME python3 probe/a100/warmup_upload_measure.py measure --runs probe/a100-reh-p85/out \\
      probe/a100-reh-p85b/out --dir probe/a100-upload/p85b --alternates --jobs 4
Then (coordinator, with the operator's standing go at >= 85): probe/calib/upload_gate.py <dir>/candidate.jsonl <dir>/pred.json (prints rows
below their best earlier official score: the board keeps only the latest upload), submit/ledger.py register / sent / scored.
Pull the runs first (infra/vast/package_watch.sh ID pull with the run's TAG / LOCAL / RUN_DIR / OUT) so OUT is current."""
from __future__ import annotations

import argparse, json, statistics, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
WARMUP = ROOT / "data/benchmark_warmup.jsonl"


def read_jsonl(p: Path) -> list[dict]:
    out = []
    for l in Path(p).read_text(errors="replace").splitlines():
        try:
            r = json.loads(l) if l.strip() else None
        except ValueError:
            continue
        if isinstance(r, dict):
            out.append(r)
    return out


def safe(n: str) -> str:
    import re
    return re.sub(r"[^A-Za-z0-9_.-]", "_", n)


def valid(row: dict, proof: str) -> str | None:
    """None when the proof may be uploaded for this row, else why not."""
    from scorer.forbidden import check_forbidden
    from scorer.tokenize import split_declaration
    if not proof or not proof.strip():
        return "empty"
    if split_declaration(proof.rstrip(), row["statement"]) is None:
        return "does not start with the exact statement + :="
    f = check_forbidden(proof)
    return f"forbidden: {f}" if f is not None else None


def candidates(rows: list[dict], runs: list[Path]) -> dict:
    """{row: [cand, ...]} from every run's export and banked bests; cand = {proof, stored, src}."""
    by = {r["name"]: [] for r in rows}
    for run in runs:
        tag = run.parent.name if run.name == "out" else run.name
        if (run / "proofs.jsonl").exists() and not (run / "summary.json").exists():
            print(f"WARN {run}: proofs.jsonl without summary.json (export interrupted?)", file=sys.stderr)
        for e in read_jsonl(run / "proofs.jsonl") if (run / "proofs.jsonl").exists() else []:
            if e.get("name") in by and e.get("stored_score") is not None:
                by[e["name"]].append({"proof": e["proof"], "stored": float(e["stored_score"]), "src": f"{tag}:export:{e.get('source')}"})
        for r in rows:
            sp = run / "work" / safe(r["name"]) / "state.json"
            try:
                b = json.loads(sp.read_text()).get("best") or {}
            except (OSError, ValueError):
                continue
            if b.get("proof") and b.get("score") is not None:
                by[r["name"]].append({"proof": b["proof"], "stored": float(b["score"]), "src": f"{tag}:agent-best"})
            # 2026-10-31: the eager end pipeline's polished proofs (OUT/end-pipe/<row>/<sha>/end/finals.json) are in the export only at the
            # job's end; count them mid-run too (stored = the pipeline's own meter; `measure` re-measures every pick on the official meter)
            for ef in sorted(f for st in ("end", "r10", "r10b") for f in (run / "end-pipe" / safe(r["name"])).glob(f"*/{st}/finals.json")):   # b94a: + the r10 rounds
                try:
                    e = (json.loads(ef.read_text()) or {}).get(r["name"]) or {}
                except (OSError, ValueError):
                    continue
                if e.get("proof") and e.get("score") is not None:
                    by[r["name"]].append({"proof": e["proof"], "stored": float(e["score"]),
                                          "src": f"{tag}:end-pipe:{ef.parent.parent.name}" + ("" if ef.parent.name == "end" else f":{ef.parent.name}")})
    return by


def pick(rows: list[dict], by: dict) -> tuple[list[dict], dict]:
    chosen, rep = [], {}
    for r in rows:
        n = r["name"]; ok, rej = [], []
        for c in by[n]:
            why = valid(r, c["proof"])
            (rej if why else ok).append({**c, "why": why} if why else c)
        ok.sort(key=lambda c: -c["stored"])
        if ok:
            chosen.append({"name": n, "proof": ok[0]["proof"].rstrip() + "\n", "stored": ok[0]["stored"], "src": ok[0]["src"]})
        else:
            chosen.append({"name": n, "proof": r["src"].rstrip() + "\n", "stored": 33.33, "src": "seed (no valid candidate)"})
        rep[n] = {"pick": chosen[-1]["src"], "stored": chosen[-1]["stored"],
                  "others": [{"src": c["src"], "stored": c["stored"]} for c in ok[1:6]], "rejected": [{"src": c["src"], "why": c["why"]} for c in rej]}
    return chosen, rep


def eval_official(name: str, proof: str, scratch: Path) -> dict:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=scratch) as fh:
        fh.write(proof); pf = fh.name
    t0 = time.time()
    p = subprocess.run([sys.executable, str(ROOT / "probe/calib/eval_official.py"), name, pf, "--all-pins", "--scratch",
                        str(scratch / f"ev_{safe(name)[:40]}_{abs(hash(proof)) % 10**8}")], capture_output=True, text=True, timeout=5400, cwd=ROOT)
    try:
        return json.loads(p.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        return {"row": name, "ok": False, "error": (p.stderr or p.stdout)[-400:], "seconds": round(time.time() - t0, 1)}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("cmd", choices=["pick", "measure"])
    ap.add_argument("--runs", nargs="+", required=True, help="pulled run out dirs (probe/a100-reh-<tag>/out)")
    ap.add_argument("--dir", required=True, help="output directory")
    ap.add_argument("--rows", default=str(WARMUP))
    ap.add_argument("--target", type=float, default=85.0)
    ap.add_argument("--alternates", action="store_true", help="measure the runner-up too when the top two stored scores are within --alt-gap")
    ap.add_argument("--alt-gap", type=float, default=0.3)
    ap.add_argument("--jobs", type=int, default=3)
    a = ap.parse_args()
    rows = read_jsonl(Path(a.rows)); d = Path(a.dir); d.mkdir(parents=True, exist_ok=True)
    assert len(rows) == 15, f"{a.rows}: {len(rows)} rows, expected the warm-up 15"
    by = candidates(rows, [Path(x) for x in a.runs])
    chosen, rep = pick(rows, by)
    stored_mean = statistics.mean(c["stored"] for c in chosen)
    print(f"pick: stored mean {stored_mean:.3f} over 15 rows from {', '.join(a.runs)}")
    for c in chosen:
        print(f"  {c['name'][:58]:58s} {c['stored']:7.2f}  {c['src']}")
    if a.cmd == "pick":
        (d / "candidate.jsonl").write_text("".join(json.dumps({"name": c["name"], "proof": c["proof"]}, ensure_ascii=False) + "\n" for c in chosen))
        (d / "pick.json").write_text(json.dumps({"stored_mean": round(stored_mean, 4), "runs": a.runs, "rows": rep}, indent=1, ensure_ascii=False))
        print(f"wrote {d}/candidate.jsonl, {d}/pick.json (stored scores only: run `measure` in a capped unit before any upload)")
        return 0
    # measure: the pick (and close runner-ups) through the official-matching meter
    scratch = d / "scratch"; scratch.mkdir(exist_ok=True)
    jobs = []
    for r, c in zip(rows, chosen):
        jobs.append((r["name"], c["src"], c["proof"]))
        if a.alternates:
            ok = sorted((x for x in by[r["name"]] if valid(r, x["proof"]) is None and x["src"] != c["src"]), key=lambda x: -x["stored"])
            if ok and c["stored"] - ok[0]["stored"] <= a.alt_gap and ok[0]["proof"].strip() != c["proof"].strip():
                jobs.append((r["name"], ok[0]["src"], ok[0]["proof"].rstrip() + "\n"))
    res: dict = {}
    with ThreadPoolExecutor(max(1, a.jobs)) as ex, (d / "measure.jsonl").open("a") as fh:
        for (n, src, proof), m in zip(jobs, ex.map(lambda j: eval_official(j[0], j[2], scratch), jobs)):
            rec = {"name": n, "src": src, **{k: m.get(k) for k in ("ok", "tokens_official", "hb_direct", "hb_official_pred", "L", "H", "Z", "score_pred", "error", "seconds")}}
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n"); fh.flush()
            res.setdefault(n, []).append((rec, proof))
    final, pred = [], {}
    for r, c in zip(rows, chosen):
        good = [(rec, p) for rec, p in res.get(r["name"], []) if rec.get("ok") and rec.get("score_pred") is not None and (rec.get("Z") or 0) >= 100]
        if good:
            rec, p = max(good, key=lambda x: x[0]["score_pred"])
        else:   # nothing measured cleanly: keep the stored pick, flagged
            rec, p = {"src": c["src"], "score_pred": None, "error": "no clean measurement"}, c["proof"]
        final.append({"name": r["name"], "proof": p})
        pred[r["name"]] = {"score": rec.get("score_pred"), "source": f"open A100 from-seed lineage {rec.get('src')} (eval_official --all-pins)",
                           "L": rec.get("L"), "H": rec.get("H"), "Z": rec.get("Z")}
    scored = [v["score"] for v in pred.values() if v["score"] is not None]
    mean = statistics.mean(scored) if len(scored) == 15 else None
    pred["_meta"] = {"predicted_mean": mean, "measured_rows": len(scored), "target": a.target, "runs": a.runs,
                     "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (d / "candidate.jsonl").write_text("".join(json.dumps(x, ensure_ascii=False) + "\n" for x in final))
    (d / "pred.json").write_text(json.dumps(pred, indent=1, ensure_ascii=False))
    for r in rows:
        v = pred[r["name"]]; print(f"  {r['name'][:58]:58s} {v['score'] if v['score'] is not None else 'n/a':>8}  {v['source']}")
    if mean is None:
        print(f"NO-GO: only {len(scored)} of 15 rows measured cleanly (see {d}/measure.jsonl)"); return 1
    print(f"predicted official warm-up mean {mean:.3f}: {'GO' if mean >= a.target else 'NO-GO'} (target {a.target}); files {d}/candidate.jsonl {d}/pred.json")
    return 0 if mean >= a.target else 3


if __name__ == "__main__":
    raise SystemExit(main())
