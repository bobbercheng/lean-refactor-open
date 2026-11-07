#!/usr/bin/env python3
"""postfast snapshot readout (post-hoc measurement, 2026-11-05): the score a DEADLINE STOP would keep, from the logs alone.

The uploaded post-step (a25416f5 open_post.improve_row) adopts a candidate only after pins, the paired re-reading, the floor and the
audit, then logs `row#K <name>: pass i adopted <op> (a -> b)` and sets the row's incumbent to it; a stop (_Stop: row wall, step wall,
budget) keeps the last confirmed incumbent. So the proof a stop at time T would keep is the row's last adoption logged at or before T
(across the row's pipelined CLI passes), and its score is b. This reads, per host dir (pf_drive --out): START, rNN/pP.log; per row
the export line otherwise. Scores are reported like the CLI's stored_score (rounded to 2 decimals).

usage: snapshot.py export.jsonl T1,T2,...|inf host_dir [host_dir ...] [--target 82.556] [--windows windows.json] [--json out.json]
                   [--check] [--adopt-dir [--adopt-file adoptions.jsonl]] [--emit DIR]
  T in seconds from each host's own START ("inf" = everything logged). --windows: per-row T map {name: seconds} (overlap readout).
Self-check (--check): at T=inf, every row that finished all its passes must equal its passes.jsonl final stored_score.
Without --adopt-dir / --emit the readout and its output are exactly as before (the new keys "adopt" / "emit" appear only with them).
CAPPED passes (pf_drive --cap stopped the worker; passes.jsonl status "capped"): a cap is a deadline stop, so a capped pass's
  adoptions logged at or before T count, in the readout as in --emit (the CLI confirmed them before it was stopped). pf_drive itself
  keeps only COMPLETED pass outputs (a stopped CLI writes none), so for a row capped after an adoption the readout / --emit at T >= that
  adoption (T=inf included) is AHEAD of pf_drive's merged proofs.post.jsonl and its passes.jsonl stored_score. --check therefore
  counts a row whose last pass was capped as not finished (check.capped_rows: their number, present only when > 0), and the --emit
  self-check skips such rows (rows_capped_skipped).

--adopt-dir (2026-11-05): each host dir's adoption side log (pf_worker.py PF_ADOPT_LOG, default file name adoptions.jsonl; one JSON line
  per audit the CLI ran: t, row, pass_cli, audit, why, decl, pid, w0, and when read from improve_row's frame pass_inner, op, score,
  tokens, heartbeats, inc_score, before). improve_row (a25416f5) audits only a candidate that passed its pins, the paired re-reading
  and the floor, and adopts it iff the audit is "clean" or "skipped" (any other status: the next candidate), so per (row, CLI pass) the
  records with audit in {clean, skipped}, in time order, pair one-to-one with the pass's `pass k adopted <op> (a -> b)` lines in file
  order. A pass pairs only when the counts agree and every pair agrees on what both sides know (op, the 4-decimal score b, the inner
  pass, the record's time not after the log line's second); else none of its events uses a record (reported). When a (row, pass) has
  records of several workers (w0), only the latest worker's are used (a re-run pass rewrote p<P>.log but appended to the side log).
--emit DIR: snapshot_<T>.jsonl per T (and snapshot_windows.jsonl with --windows), one line per export row in export order: the line a
  deadline stop at T would leave in proofs.post.jsonl. A row with no adoption at or before T: its export line, byte for byte. Else the
  row's last adoption at or before T, written like open_post.post_out_record (a25416f5):
    name, source "post"            known;
    proof                          the record's decl (the audited text = the adopted decl) .rstrip() + "\n" (post_out_record's form);
    stored_score                   round(score, 2) with the record's exact score (the CLI's own value); without it round(b, 2) of the
                                   log line (b is printed to 4 decimals: may differ by 0.01 at a rounding boundary);
    tokens, heartbeats             the record's (improve_row's mc: the kept, worse-of-two reading); null when the record lacks them;
    post_gain                      round(score - before, 4), before = the CLI pass's r0 score (record, else passes.jsonl "before"; the
                                   log line's a is the paired incumbent reading, not r0); null when neither is known;
    post_ops                       the ops of the pass's adoption lines up to this one (= the CLI's chain);
    post_from                      "post" when an earlier CLI pass of the row adopted (its output was the pass's input), else the export
                                   line's source;
    audit                          the record's audit status (= the chain's last audit; post_out_record falls back to the input line's
                                   audit only when that is empty, which "clean" / "skipped" never are).
  Without a paired record, the last adoption of a CLI pass that ended "adopted" takes that pass's rNN/pP/proofs.post.jsonl line k byte
  for byte (exact in every field). An adoption known neither way (an inner adoption of a multi-adoption pass without the side log) is
  skipped back to the row's latest known adoption before it (or the export line) and counted as "behind" the readout. An adoption of a
  CLI pass whose passes.jsonl status is not "adopted" or "capped" (worker_failed, error: pf_drive kept the pass's input) counts only
  while T is before that pass's t_end (pf_drive time, ~ START); a "capped" pass's adoptions count at T >= their log time (CAPPED
  above: never compared with t_end). Self-check (always in --emit): at T=inf, for every host with a final proofs.post.jsonl and every
  row of it that finished all passes (its last pass not capped), the emitted proof must equal the final line's proof (and the full
  lines are compared too).
"""
from __future__ import annotations

import argparse, datetime as dt, json, re, statistics, sys
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("export")
ap.add_argument("times")
ap.add_argument("hosts", nargs="+")
ap.add_argument("--target", type=float, default=82.556)
ap.add_argument("--windows", default=None)
ap.add_argument("--json", default=None)
ap.add_argument("--check", action="store_true")
ap.add_argument("--adopt-dir", action="store_true", help="pair each host dir's adoption side log with the adoption log lines")
ap.add_argument("--adopt-file", default="adoptions.jsonl", help="the side log's file name inside each host dir")
ap.add_argument("--emit", default=None, help="write snapshot_<T>.jsonl files (the proofs.post.jsonl a stop at T would leave) here")
a = ap.parse_args()

recs = [json.loads(l) for l in Path(a.export).read_text().splitlines() if l.strip()]
names = [r["name"] for r in recs]
ADOPT = re.compile(r"^\[(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ)\] \[post\] row#(\d+) .*?: pass (\d+) adopted (\S+) \(([-\d.]+) -> ([-\d.]+)\)")


def ts(s: str) -> float:
    return dt.datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc).timestamp()


events: dict[int, list] = {}    # row index -> [(t_rel, cli_pass, inner, op, a, b)]
finals: dict[int, float] = {}   # row index -> passes.jsonl stored_score after its last finished pass
last_pass: dict[int, int] = {}
last_status: dict[int, str] = {}   # row index -> passes.jsonl status of that last pass ("capped": pf_drive --cap stopped it)
host_of: dict[int, str] = {}
for h in a.hosts:
    hd = Path(h)
    t0 = ts(hd.joinpath("START").read_text().strip())
    for rd in sorted(hd.glob("r[0-9][0-9]")):
        k = int(rd.name[1:])
        host_of[k] = hd.name
        for lp in sorted(rd.glob("p*.log"), key=lambda p: int(p.stem[1:])):
            p = int(lp.stem[1:])
            for line in lp.read_text(errors="replace").splitlines():
                m = ADOPT.match(line)
                if m and int(m.group(2)) == k:
                    events.setdefault(k, []).append((ts(m.group(1)) - t0, p, int(m.group(3)), m.group(4), float(m.group(5)), float(m.group(6))))
    pj = hd / "passes.jsonl"
    if pj.exists():
        for l in pj.read_text().splitlines():
            if not l.strip():
                continue
            e = json.loads(l)
            k = names.index(e["name"])
            if e["pass_"] >= last_pass.get(k, 0):
                last_pass[k] = e["pass_"]
                finals[k] = e["stored_score"]
                last_status[k] = e.get("status")
for k in events:
    events[k].sort()

windows = json.loads(Path(a.windows).read_text()) if a.windows else None


def snap(T: float | None, per_row: dict | None = None) -> list[float]:
    out = []
    for k, r in enumerate(recs):
        Tk = per_row.get(r["name"], T) if per_row else T
        s = r["stored_score"]
        for (t, p, i, op, x, b) in events.get(k, []):
            if Tk is None or t <= Tk:
                s = round(b, 2)
        out.append(s)
    return out


res = {"rows": len(recs), "export_mean": round(statistics.mean(r["stored_score"] for r in recs), 4), "snapshots": {}}
for tok in a.times.split(","):
    T = None if tok == "inf" else float(tok)
    sc = snap(T)
    res["snapshots"][tok] = round(statistics.mean(sc), 4)
# time to target at 60 s resolution over the logged events
allt = sorted({t for ev in events.values() for (t, *_r) in ev})
first = None
for t in allt:
    if statistics.mean(snap(t)) >= a.target - 1e-9:
        first = round(t, 1)
        break
res["first_reached_target_s"] = first
res["target"] = a.target
res["last_event_s"] = round(allt[-1], 1) if allt else None
if windows:
    res["windows_snapshot"] = round(statistics.mean(snap(None, windows)), 4)
if a.check:
    bad = []
    inf = snap(None)
    # a pass 7 stopped by pf_drive --cap did not finish: passes.jsonl keeps the last completed pass's score while its adoptions count
    finished = lambda k: last_pass.get(k) == 7 and last_status.get(k) != "capped"
    for k, f in finals.items():
        if finished(k) and abs(inf[k] - f) > 0.0051:
            bad.append((names[k], inf[k], f))
    res["check"] = {"finished_rows": sum(1 for k in finals if finished(k)), "mismatches": bad[:20], "n_mismatch": len(bad)}
    n_capped = sum(1 for k in finals if last_status.get(k) == "capped")
    if n_capped:   # rows whose last pass was capped (never "finished"); only in capped runs: a run without --cap reads as before
        res["check"]["capped_rows"] = n_capped


# ------------------------------------------------------------------------------------------------ --adopt-dir / --emit (module docstring)
ADOPTED = ("clean", "skipped")   # improve_row adopts iff the audit status is one of these


def _load_adoptions(path: Path, info: dict) -> dict:
    """{(row name, pass_cli): [records, latest worker only, time order]} of one host's side log."""
    by: dict = {}
    for line in path.read_text(errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            info["bad_lines"] += 1
            continue
        if not isinstance(r, dict) or "row" not in r or "decl" not in r:
            info["bad_lines"] += 1
            continue
        by.setdefault((r["row"], r.get("pass_cli")), []).append(r)
    for key, lst in by.items():
        w0s = {x.get("w0") for x in lst}
        if len(w0s) > 1:
            last = max(w0s, key=lambda w: (w is not None, w or 0.0))
            info["stale_records_dropped"] += sum(1 for x in lst if x.get("w0") != last)
            lst[:] = [x for x in lst if x.get("w0") == last]
        lst.sort(key=lambda x: float(x.get("t") or 0.0))   # stable: one worker writes its records in order
        info["records"] += len(lst)
        info["adopted_records"] += sum(1 for x in lst if x.get("audit") in ADOPTED)
    return by


def _pair_ok(e: dict, r: dict) -> str | None:
    """None when the record agrees with the log line on everything both know, else what differs."""
    if "op" in r and r["op"] != e["op"]:
        return f"op {r['op']} != {e['op']}"
    if isinstance(r.get("score"), (int, float)) and f"{float(r['score']):.4f}" != e["b_s"]:
        return f"score {float(r['score']):.4f} != {e['b_s']}"
    if isinstance(r.get("pass_inner"), int) and r["pass_inner"] != e["inner"]:
        return f"inner pass {r['pass_inner']} != {e['inner']}"
    if isinstance(r.get("t"), (int, float)) and not (e["t_abs"] - 30.0 <= float(r["t"]) < e["t_abs"] + 1.5):
        return f"record time {float(r['t']):.1f} vs log second {e['t_abs']:.0f}"
    return None


def adopt_mode() -> dict:
    raw = [l for l in Path(a.export).read_text().splitlines() if l.strip()]   # the export lines byte for byte (recs is parsed from them)
    out: dict = {}
    info = {"hosts_with_log": [], "records": 0, "adopted_records": 0, "bad_lines": 0, "stale_records_dropped": 0, "events": 0,
            "events_paired": 0, "passes_with_events": 0, "passes_paired": 0, "passes_without_records": 0, "count_mismatch": [],
            "pair_mismatch": [], "vs_pass_output": {"compared": 0, "equal": 0, "diff_fields": {}}}
    evp: dict = {}       # k -> {cli pass: [event dicts in log order]}
    hdir: dict = {}      # k -> host dir Path
    pinfo: dict = {}     # (k, cli pass) -> passes.jsonl event
    n_pass = 0
    for h in a.hosts:
        hd = Path(h)
        t0 = ts(hd.joinpath("START").read_text().strip())
        pj = hd / "passes.jsonl"
        if pj.exists():
            for l in pj.read_text().splitlines():
                if l.strip():
                    e = json.loads(l)
                    pinfo[(names.index(e["name"]), e["pass_"])] = e
                    n_pass = max(n_pass, int(e["pass_"]))
        for rd in sorted(hd.glob("r[0-9][0-9]")):
            k = int(rd.name[1:])
            hdir[k] = hd
            for lp in sorted(rd.glob("p*.log"), key=lambda p: int(p.stem[1:])):
                p = int(lp.stem[1:])
                lst = []
                for line in lp.read_text(errors="replace").splitlines():
                    m = ADOPT.match(line)
                    if m and int(m.group(2)) == k:
                        lst.append({"k": k, "p": p, "j": len(lst), "t_abs": ts(m.group(1)), "t": ts(m.group(1)) - t0,
                                    "inner": int(m.group(3)), "op": m.group(4), "a": float(m.group(5)), "b": float(m.group(6)),
                                    "b_s": m.group(6), "rec": None})
                if lst:
                    evp.setdefault(k, {})[p] = lst
        recs_by = {}
        if a.adopt_dir and (hd / a.adopt_file).exists():
            info["hosts_with_log"].append(str(hd))
            recs_by = _load_adoptions(hd / a.adopt_file, info)
        for k, byp in evp.items():
            if hdir.get(k) != hd:
                continue
            for p, evs in sorted(byp.items()):
                info["events"] += len(evs); info["passes_with_events"] += 1
                rl = [x for x in recs_by.get((names[k], p), []) if x.get("audit") in ADOPTED]
                if not rl:
                    info["passes_without_records"] += 1
                    continue
                if len(rl) != len(evs):
                    info["count_mismatch"].append({"row": k, "pass": p, "log_lines": len(evs), "adopted_records": len(rl)})
                    continue
                why = next((w for w in (_pair_ok(e, r) for e, r in zip(evs, rl)) if w), None)
                if why:
                    info["pair_mismatch"].append({"row": k, "pass": p, "why": why})
                    continue
                for e, r in zip(evs, rl):
                    e["rec"] = r
                info["passes_paired"] += 1; info["events_paired"] += len(evs)

    def status(k, p):
        return (pinfo.get((k, p)) or {}).get("status")

    def taken(k, p):   # pf_drive used the pass's output as the next pass's input (unknown: still running, as the readout assumes)
        return status(k, p) in ("adopted", None)

    pass_lines: dict = {}

    def pass_output_line(k, p):
        key = (k, p)
        if key not in pass_lines:
            f = hdir[k] / f"r{k:02d}" / f"p{p}" / "proofs.post.jsonl"
            ls = [l for l in f.read_text().splitlines() if l.strip()] if f.exists() else []
            pass_lines[key] = ls[k] if len(ls) == len(recs) else None
        return pass_lines[key]

    def from_record(e) -> dict:
        k, p, r = e["k"], e["p"], e["rec"]
        exp = recs[k]
        exact = r.get("score") if isinstance(r.get("score"), (int, float)) and not isinstance(r.get("score"), bool) else None
        s = float(exact) if exact is not None else e["b"]
        before = r.get("before")
        if not isinstance(before, (int, float)):
            before = (pinfo.get((k, p)) or {}).get("before")
        earlier = any(pp < p and taken(k, pp) for pp in evp.get(k, {}))
        return {"name": exp["name"], "proof": str(r["decl"]).rstrip() + "\n", "source": "post",
                "post_from": "post" if earlier else exp.get("source"), "stored_score": round(s, 2), "tokens": r.get("tokens"),
                "heartbeats": r.get("heartbeats"), "post_gain": round(s - float(before), 4) if isinstance(before, (int, float)) else None,
                "post_ops": [x["op"] for x in evp[k][p][:e["j"] + 1]], "audit": r.get("audit") or exp.get("audit")}

    def line_of(e):
        """(raw JSON line, source) of the proofs.post.jsonl line a stop right after event e would leave; (None, "unknown")."""
        k, p = e["k"], e["p"]
        last = e["j"] == len(evp[k][p]) - 1
        if e["rec"] is not None:
            return json.dumps(from_record(e), ensure_ascii=False), "record"
        if last and status(k, p) == "adopted":
            po = pass_output_line(k, p)
            if po is not None:
                return po, "pass_output"
        return None, "unknown"

    vs = info["vs_pass_output"]   # every paired pass's last adoption: the record-built line against the CLI's own output line
    for k, byp in evp.items():
        for p, lst in byp.items():
            e = lst[-1]
            if e["rec"] is None or status(k, p) != "adopted" or pass_output_line(k, p) is None:
                continue
            got, want = from_record(e), json.loads(pass_output_line(k, p))
            diff = sorted(f for f in set(got) | set(want) if got.get(f) != want.get(f))
            vs["compared"] += 1; vs["equal"] += not diff
            for f in diff:
                vs["diff_fields"][f] = vs["diff_fields"].get(f, 0) + 1

    def emit_row(k, T):
        """(raw line, source, behind: the line is older than the row's last counted adoption)."""
        evs = []
        for p, lst in evp.get(k, {}).items():
            for e in lst:
                if T is not None and e["t"] > T:
                    continue
                st, te = status(k, p), (pinfo.get((k, p)) or {}).get("t_end")
                if st not in ("adopted", "capped", None) and (T is None or (isinstance(te, (int, float)) and te <= T)):
                    continue   # a void pass (pf_drive kept its input), once it has ended; a capped pass is a deadline stop
                evs.append(e)
        evs.sort(key=lambda e: (e["t"], e["p"], e["j"]))
        for i in range(len(evs) - 1, -1, -1):
            line, src = line_of(evs[i])
            if line is not None:
                return line, src, i != len(evs) - 1
        return raw[k], "export", bool(evs)

    def emit(Tmap) -> tuple[list, dict]:
        lines, srcs, behind = [], {}, []
        for k in range(len(recs)):
            line, src, bh = emit_row(k, Tmap(k))
            lines.append(line); srcs[src] = srcs.get(src, 0) + 1
            if bh:
                behind.append(names[k])
        return lines, {"sources": srcs, "n_behind": len(behind), "behind": behind[:20]}

    if a.emit:
        od = Path(a.emit); od.mkdir(parents=True, exist_ok=True)
        files = {}
        jobs = []
        for tok in a.times.split(","):
            T = None if tok == "inf" else float(tok)
            jobs.append((tok, (lambda k, T=T: T), T))
        if windows:
            jobs.append(("windows", lambda k: windows.get(names[k], None), "windows"))
        for tok, Tmap, T in jobs:
            lines, meta = emit(Tmap)
            (od / f"snapshot_{tok}.jsonl").write_text("".join(l + "\n" for l in lines))
            sc = [json.loads(l).get("stored_score") for l in lines]
            ro = snap(None, windows) if T == "windows" else snap(T)
            diff = [names[k] for k in range(len(recs)) if abs(float(sc[k]) - float(ro[k])) > 1e-9]
            files[tok] = dict(path=str(od / f"snapshot_{tok}.jsonl"), mean=round(statistics.mean(float(x) for x in sc), 4),
                              readout_mean=round(statistics.mean(ro), 4), n_differs_from_readout=len(diff), differs=diff[:20], **meta)
        inf_lines, _m = emit(lambda k: None)
        chk = {"hosts": [], "rows_compared": 0, "proof_mismatch": [], "line_mismatch": [], "n_pass": n_pass, "rows_capped_skipped": 0}
        for h in a.hosts:
            hd = Path(h)
            fin = hd / "proofs.post.jsonl"
            rc = (hd / "RC").read_text().strip() if (hd / "RC").exists() else None
            if not fin.exists():
                continue
            fl = [l for l in fin.read_text().splitlines() if l.strip()]
            if len(fl) != len(recs):
                continue
            chk["hosts"].append({"host": str(hd), "rc": rc})
            for k in range(len(recs)):
                if hdir.get(k) != hd or (pinfo.get((k, n_pass)) is None):
                    continue   # not this host's row, or it did not finish all passes
                if status(k, n_pass) == "capped":   # stopped in its last pass: the merged line is the last COMPLETED pass's output
                    chk["rows_capped_skipped"] += 1
                    continue
                chk["rows_compared"] += 1
                got, want = json.loads(inf_lines[k]), json.loads(fl[k])
                if got.get("proof") != want.get("proof"):
                    chk["proof_mismatch"].append(names[k])
                elif got != want:
                    chk["line_mismatch"].append({"row": names[k], "fields": sorted(f for f in set(got) | set(want) if got.get(f) != want.get(f))})
        chk["n_proof_mismatch"], chk["n_line_mismatch"] = len(chk["proof_mismatch"]), len(chk["line_mismatch"])
        out["emit"] = {"dir": str(od), "files": files, "self_check_inf": chk}
    if a.adopt_dir:
        out["adopt"] = info
    return out


if a.adopt_dir or a.emit:
    res.update(adopt_mode())
print(json.dumps(res, indent=1))
if a.json:
    Path(a.json).write_text(json.dumps(res, indent=1))
