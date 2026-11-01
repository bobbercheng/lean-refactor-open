#!/usr/bin/env python3
"""Knowledge discovery from a line's own runs (2026-10-08: discover the knowledge from the A100 harness's
trajectories). It mines what a line actually learned, from ground truth rather than from the model's own notes.md:

  winning edits  consecutive new bests per problem, from each run's verified.jsonl (full proofs), as diffs with their score, token and
                 heartbeat deltas; the line's first best is diffed against the reference;
  dead names     identifiers that failed as unknown in the line's compiles and never appear in one of its compiling proofs;
  techniques     the tactics and library names that winning edits add or remove, pooled across problems.

--write puts the wins and dead names into the line's own ledger (state.json "ledger"), which the next pass's first message shows
(Workspace.digest). Only the given runs are read. Mixing serving lines (e.g. z.ai runs into the self-hosted A100 line, whose public
entry must stay open-weight only) is refused unless --allow-mixed; internal* runs are always refused.

  python3 harness/discover.py --runs fresh-a100-p1,fresh-a100-p2,fresh-a100-p3 --work-root harness/work_fresh-a100 \
      [--write] [--report docs/discovery/fresh-a100.md]
"""
from __future__ import annotations

import argparse, collections, contextlib, difflib, gzip, hashlib, json, os, re, sys, time, zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration, tokens  # noqa: E402
from harness.leantools import ROWS, HBS, _UNKNOWN_RX  # noqa: E402

TACTICS = {"grind", "simp", "simp_all", "simp_rw", "simpa", "dsimp", "omega", "aesop", "decide", "norm_num", "ring", "ring_nf", "linarith",
           "nlinarith", "positivity", "field_simp", "linear_combination", "exact", "refine", "apply", "rw", "rwa", "erw", "calc", "induction",
           "cases", "rcases", "obtain", "constructor", "use", "exists", "intro", "intros", "rintro", "have", "show", "change", "convert",
           "congr", "gcongr", "ext", "funext", "subst", "contradiction", "exfalso", "by_contra", "split", "split_ifs", "unfold", "solve_by_elim",
           "tauto", "trivial", "rfl", "assumption", "all_goals", "any_goals", "first", "try", "case", "next", "<;>", "·", "fun", "only"}


PROBE_NAME = re.compile(r"placeholder|marker|does_not_exist|_todo|^h\d|^ih\b|^foo|^bar\b", re.I)   # the model's own probe names


def _readable_lines(f: Path, op) -> list[str]:
    """The lines of a damaged (truncated / corrupt gzip) trajectory up to the damage."""
    out = []
    try:
        with op(f, "rt", errors="replace") as h:
            for l in h:
                out.append(l.rstrip("\n"))
    except (OSError, EOFError, zlib.error):
        pass
    return out


def _state_lock(ws_root: Path, timeout: float = 300.0):
    from harness.statelock import state_lock
    return state_lock(ws_root, timeout=timeout)


def strings(x):
    if isinstance(x, str):
        yield x
    elif isinstance(x, dict):
        for v in x.values():
            yield from strings(v)
    elif isinstance(x, list):
        for v in x:
            yield from strings(v)


def dirname(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", name)


def body(decl: str, row: dict) -> str:
    return split_declaration(decl.rstrip(), row["statement"]) or decl


def diff(a: str, b: str) -> list[str]:
    return [l for l in difflib.unified_diff(a.splitlines(), b.splitlines(), lineterm="", n=0) if l[:1] in "+-" and not l.startswith(("+++", "---"))]


def features(lines: list[str]) -> collections.Counter:
    c = collections.Counter()
    for l in lines:
        for t in tokens(l[1:]):
            if t in TACTICS:
                c[t] += 1
            elif "." in t and re.match(r"^[A-Za-z_][\w']*(\.[\w'!?₀-₉]+)+$", t) and not re.match(r"^[a-z]\w{0,2}\.\d", t):
                c["lemma:" + t] += 1
    return c


TECH_LABEL = {"only": "`only` lists (simp/grind only)", "fun": "fun (term mode)", "·": "· bullets", "<;>": "<;> combinator", "exact": "exact (term)",
              "have": "have", "rw": "rw", "simp": "simp", "intro": "intro", "refine": "refine", "obtain": "obtain", "rcases": "rcases"}
LIB_NAME = re.compile(r"^[A-Z][\w']*(\.[\w'!?₀-₉]+)+$")   # namespaced library or project names; local projections like h.symm are left out


def write_kg(a, runs, models, recs, out, pooled, mism) -> None:
    """One line's knowledge as nodes/edges for the knowledge-graph page (docs/kg): problems -> techniques their winning edits added or
    removed -> library names used in winning edits -> names that do not exist here. Problem-specific; the page keeps one view per line."""
    v = a.kg_view; nodes, edges, used_t, used_l, used_d = [], [], {}, set(), set()
    now = time.strftime("%Y-%m-%d", time.gmtime())
    for name, o in sorted(out.items()):
        pid = f"{v}:p:{name}"; edits = [w for w in o["wins"] if w["kind"] == "edit"]
        top = sorted(edits, key=lambda w: -w["d_score"])[:4]
        nodes.append({"id": pid, "kind": "problem", "view": v, "label": f"{name.split('.')[-1]} · {o['final']:.2f}", "status": "active", "since": now,
                      "summary": f"{name}: best {o['final']:.2f} after {len(edits)} targeted winning edits and {len(o['wins']) - len(edits)} rewrite(s) in this line.",
                      "edits": [{"run": w["run_id"], "check": w["check"], "d_score": w["d_score"], "d_tokens": w["d_tokens"], "d_hb": w["d_heartbeats"],
                                 "diff": w["diff"][:600]} for w in top], "dead": o["dead"][:12]})
        for f, (n_add, gain, n_rm) in o["pf"].items():
            if f.startswith("lemma:"):
                nm = f[6:]
                if n_add and LIB_NAME.match(nm):
                    edges.append([pid, "used_in_win", f"{v}:l:{nm}", n_add]); used_l.add(nm)
            else:
                if n_add:
                    edges.append([pid, "won_with", f"{v}:t:{f}", round(gain, 2)]); used_t[f] = True
                if n_rm:
                    edges.append([pid, "won_by_removing", f"{v}:t:{f}", n_rm]); used_t[f] = True
        for dn in o["dead"][:12]:
            edges.append([pid, "unknown_here", f"{v}:d:{dn}", 1]); used_d.add(dn)
    for f in used_t:
        n_add, gain, n_rm = pooled.get(f, [0, 0.0, 0])
        nodes.append({"id": f"{v}:t:{f}", "kind": "technique", "view": v, "label": TECH_LABEL.get(f, f), "status": "active", "since": now,
                      "summary": f"Across this line: added in {n_add} winning edits (summed gain {gain:+.2f}); removed in {n_rm} winning edits."})
    for nm in sorted(used_l):
        n_add, gain, _ = pooled.get("lemma:" + nm, [0, 0.0, 0])
        nodes.append({"id": f"{v}:l:{nm}", "kind": "lemma", "view": v, "label": nm, "status": "active", "since": now,
                      "summary": f"Added in {n_add} winning edit(s) in this line (summed gain {gain:+.2f})."})
    for dn in sorted(used_d):
        nodes.append({"id": f"{v}:d:{dn}", "kind": "deadname", "view": v, "label": dn, "status": "open", "since": now,
                      "summary": "Failed as an unknown name in this line's compiles and never appears in one of its compiling proofs."})
    # legibility caps (the full lists stay in the Markdown report): techniques seen in >= 2 winning edits (or removed in >= 3), the 40 lemmas
    # with the largest summed gain
    keep_t = {f"{v}:t:{f}" for f in used_t if pooled.get(f, [0, 0, 0])[0] >= 2 or pooled.get(f, [0, 0, 0])[2] >= 3}
    keep_l = {f"{v}:l:{nm}" for nm in sorted(used_l, key=lambda nm: -pooled.get("lemma:" + nm, [0, 0.0, 0])[1])[:40]}
    nodes = [n for n in nodes if n["kind"] not in ("technique", "lemma") or n["id"] in keep_t | keep_l]
    ids = {n["id"] for n in nodes}; edges = [e for e in edges if e[0] in ids and e[2] in ids]
    meta = {"view": v, "title": a.kg_title or v, "runs": runs, "serving": sorted(map(str, models)), "records": sum(len(r) for r in recs.values()),
            "edits": sum(1 for o in out.values() for w in o["wins"] if w["kind"] == "edit"), "problems": len(out),
            "assembled": round(sum(o["final"] for o in out.values()) / max(1, len(out)), 2),
            "validation": "chains end at the stored best on every problem" if not mism else "mismatch: " + "; ".join(mism),
            "generated": time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime())}
    pth = ROOT / a.kg_json; pth.parent.mkdir(parents=True, exist_ok=True)
    pth.write_text(json.dumps({"meta": meta, "nodes": nodes, "edges": edges}, ensure_ascii=False))
    print(f"knowledge graph: {a.kg_json} ({len(nodes)} nodes, {len(edges)} edges)")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", required=True, help="comma-separated run ids, oldest first")
    ap.add_argument("--work-root", required=True, help="the line's work root, e.g. harness/work_fresh-a100")
    ap.add_argument("--write", action="store_true", help="write wins and dead names into the work root's state.json ledgers (backup kept)")
    ap.add_argument("--report", default=None, help="write a Markdown report here")
    ap.add_argument("--allow-mixed", action="store_true", help="allow runs from different serving lines (provenance models)")
    ap.add_argument("--kg-json", default=None, help="write this line's knowledge as graph nodes/edges for docs/kg (read-only; never touches state)")
    ap.add_argument("--kg-view", default="line", help="view key for --kg-json (e.g. zai, a100)")
    ap.add_argument("--kg-title", default=None, help="tab title for --kg-json")
    ap.add_argument("--ledger-only", action="store_true", help="in-run learning (2026-10-12, allowed on internal and internal pool runs): "
                    "write the line's own per-problem ledgers only; no report, no knowledge graph, and counts-only output (no names)")
    a = ap.parse_args()
    runs = [r.strip() for r in a.runs.split(",") if r.strip()]
    if a.ledger_only:
        if a.report or a.kg_json:
            sys.exit("refused: --ledger-only writes no report and no knowledge graph")
        a.write = True
    elif any(r.startswith(("internal", "internalpool")) for r in runs):   # internal/internal held-out sets and the frame internal pool (2026-10-11)
        sys.exit("refused: internal*/internalpool-* runs may not be mined into knowledge outside the run (the internal-set log); "
                 "in-run ledgers need --ledger-only")
    recs, models = collections.defaultdict(list), set()
    for r in runs:
        vf = ROOT / "probe/runs" / r / "verified.jsonl"
        if not vf.exists():
            sys.exit(f"missing {vf}")
        for l in vf.open():
            if l.strip():
                j = json.loads(l); recs[j["problem"]].append(j); models.add((j.get("provenance") or {}).get("model"))
    if len(models) > 1 and not a.allow_mixed:
        sys.exit(f"refused: the runs mix serving lines {sorted(map(str, models))}; pass --allow-mixed only if that is intended")

    out, pooled = {}, collections.defaultdict(lambda: [0, 0.0, 0])   # feature -> [wins adding it, summed d_score, wins removing it]
    for name in sorted(recs):
        row = ROWS.get(name)
        if not row:
            continue
        prev = {"proof": row["src"], "score": 33.33, "tokens": row["proof_length"], "heartbeats": HBS.get(name) or 0, "run_id": "reference"}
        prev["provenance"] = {"run_id": "reference"}
        wins = []; pf = collections.defaultdict(lambda: [0, 0.0, 0])   # per-problem: [edit wins adding, summed gain, edit wins removing]
        for j in recs[name]:   # file order = check order within a run; runs in the given order
            if float(j["score"]) <= float(prev["score"]) + 1e-9:
                continue
            d = diff(body(prev["proof"], row), body(j["proof"], row))
            w = {"run_id": (j.get("provenance") or {}).get("run_id"), "check": (j.get("provenance") or {}).get("check"),
                 "d_score": round(float(j["score"]) - float(prev["score"]), 2), "d_tokens": int(j["tokens"]) - int(prev["tokens"] or 0),
                 "d_heartbeats": int(j["heartbeats"] or 0) - int(prev["heartbeats"] or 0), "diff": "\n".join(d)[:700], "source": "discover",
                 "kind": "rewrite" if prev["run_id"] == "reference" or len(d) > 0.6 * (len(body(prev["proof"], row).splitlines()) + len(body(j["proof"], row).splitlines()))
                 else "edit"}   # rewrites (the first best, or a diff touching most lines) are already in the current best's lineage
            w["sha"] = hashlib.sha256(w["diff"].encode()).hexdigest()[:12]
            wins.append(w)
            fa, fr = features([x for x in d if x[0] == "+"]), features([x for x in d if x[0] == "-"])
            for f in (set(fa) | set(fr)) if w["kind"] == "edit" else ():   # techniques: targeted edits only, not the first rewrite
                if fa[f] > fr[f]:
                    pooled[f][0] += 1; pooled[f][1] += w["d_score"]; pf[f][0] += 1; pf[f][1] += w["d_score"]
                elif fr[f] > fa[f]:
                    pooled[f][2] += 1; pf[f][2] += 1
            prev = dict(j, run_id=(j.get("provenance") or {}).get("run_id"))
        out[name] = {"wins": wins, "final": float(prev["score"]), "dead": collections.Counter(), "pf": pf}

    # dead names from the line's trajectories (failed compiles), minus names that appear in any compiling proof of the line
    unreadable = 0
    for r in runs:
        for f in (ROOT / "probe/runs" / r / "trajectories").glob("*.jsonl*"):
            op = gzip.open if f.suffix == ".gz" else open
            try:
                lines = op(f, "rt", errors="replace").read().splitlines()
            except (OSError, EOFError, zlib.error):   # 2026-10-12 review: a truncated gzip member (driver killed mid-append): what reads, counted
                unreadable += 1; lines = _readable_lines(f, op)
            try:
                name = json.loads(lines[0]).get("problem")
            except Exception:  # noqa: BLE001
                continue
            if name not in out:
                continue
            for l in lines[1:]:
                try:
                    msg = json.loads(l)
                except Exception:  # noqa: BLE001
                    continue
                if msg.get("type") == "user" and isinstance(msg.get("message"), dict):   # Claude Code stream events (driver agent_claude_code.py)
                    msg = {"type": "message", "role": "user", "content": msg["message"].get("content")}
                if msg.get("type") != "message" or msg.get("role") != "user" or not isinstance(msg.get("content"), list):
                    continue
                for b in msg["content"]:
                    if not (isinstance(b, dict) and b.get("type") == "tool_result"):
                        continue
                    t = b.get("content") if isinstance(b.get("content"), str) else json.dumps(b.get("content"), ensure_ascii=False)
                    t = t.split("do not check it again]\n", 1)[-1]   # write_file results carry the auto-check after this marker
                    try:
                        texts = list(strings(json.loads(t)))   # decode the inner JSON so \\u escapes become the real names
                    except Exception:  # noqa: BLE001
                        texts = [t]
                    for s in texts:
                        for m in _UNKNOWN_RX.finditer(s):
                            n = (m.group(1) or m.group(2) or "").strip("`'\\")
                            if n and ("." in n or "_" in n) and len(n) > 3:   # library-style names, not misnamed local hypotheses
                                out[name]["dead"][n] += 1
    for name, o in out.items():
        proofs = "\n".join(j["proof"] for j in recs[name])
        o["dead"] = [n for n, _ in o["dead"].most_common() if n.split(".")[-1] not in proofs and not PROBE_NAME.search(n)][:30]

    # validation against the line's state: the mined chain must end at the stored best
    wr = ROOT / a.work_root; mism = []
    for name, o in out.items():
        st = wr / dirname(name) / "state.json"
        if st.exists():
            b = float((json.loads(st.read_text()).get("best") or {}).get("score") or 33.33)
            o["stored"] = b
            if abs(b - o["final"]) > 0.01:
                mism.append(f"{name}: mined {o['final']} vs stored {b}")
    print(f"{len(runs)} runs, {sum(len(v) for v in recs.values())} verified records, {sum(len(o['wins']) for o in out.values())} winning edits, "
          f"{sum(len(o['dead']) for o in out.values())} dead names over {len(out)} problems; serving {sorted(map(str, models))}")
    if unreadable:
        print(f"{unreadable} damaged trajectory file(s) read up to the damage")
    if a.ledger_only:   # counts only: problem names never reach the output
        print("validation:", "mined chains end at the stored best on every problem" if not mism else f"MISMATCH on {len(mism)} problem(s)")
    else:
        print("validation:", "mined chains end at the stored best on every problem" if not mism else "MISMATCH " + "; ".join(mism))

    if a.write:
        stamp = time.strftime("%Y%m%d-%H%M%S"); busy = 0
        for name, o in out.items():
            st = wr / dirname(name) / "state.json"
            if not st.exists():
                continue
            # --ledger-only (in-run, between batches; 2026-10-12 review): under the workspace's state lock and written atomically, so a
            # session or tool of the line that is still (or already) running never loses its pre-charge, attempts or best to this write
            try:
                with (_state_lock(st.parent) if a.ledger_only else contextlib.nullcontext()):
                    s = json.loads(st.read_text())
                    (st.parent / f"state.json.bak-discover-{stamp}").write_text(json.dumps(s, ensure_ascii=False))
                    led = s.setdefault("ledger", {})
                    have = {w.get("sha") or hashlib.sha256((w.get("diff") or "").encode()).hexdigest()[:12] for w in led.get("wins", [])}
                    led["wins"] = (led.get("wins", []) + [w for w in o["wins"] if w["sha"] not in have and w["kind"] == "edit"])[-30:]
                    led["dead_names"] = o["dead"]
                    if a.ledger_only:
                        tmp = st.with_name(f".state.json.tmp-discover-{os.getpid()}")
                        tmp.write_text(json.dumps(s, ensure_ascii=False)); os.replace(tmp, st)
                    else:
                        st.write_text(json.dumps(s, ensure_ascii=False))
            except TimeoutError:
                busy += 1
        print(f"wrote ledgers in {wr} (backups state.json.bak-discover-{stamp}): "
              f"{sum(1 for o in out.values() if o['wins'] or o['dead'])} problem(s) with wins or dead names"
              + (f"; {busy} workspace(s) busy (state lock), left unchanged" if busy else ""))

    if a.kg_json:
        write_kg(a, runs, models, recs, out, pooled, mism)

    if a.report:
        rp = ROOT / a.report; rp.parent.mkdir(parents=True, exist_ok=True)
        L = [f"# Knowledge discovered from {', '.join(runs)}", "", f"Generated {time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime())} by `harness/discover.py`. "
             f"Serving: {', '.join(sorted(map(str, models)))}. Validation: {'chains end at the stored best on every problem' if not mism else 'MISMATCH: ' + '; '.join(mism)}.", "",
             "## Techniques in winning edits (pooled across problems)", "",
             f"Targeted edits only: {sum(w['kind'] == 'edit' for o in out.values() for w in o['wins'])} edit wins; the {sum(w['kind'] == 'rewrite' for o in out.values() for w in o['wins'])} first rewrites of the reference are left out.", "",
             "| added in an edit win | wins | summed score gain | wins removing it |", "|---|---|---|---|"]
        for f, (n, g, rm) in sorted(pooled.items(), key=lambda x: -x[1][1])[:30]:
            L.append(f"| `{f}` | {n} | {g:+.2f} | {rm} |")
        L += ["", "## Per problem", ""]
        for name, o in sorted(out.items(), key=lambda x: x[1]["final"]):
            L.append(f"### {name}: {o['final']} after {len(o['wins'])} winning edits")
            for w in sorted(o["wins"], key=lambda w: -w["d_score"])[:4]:
                L += [f"- {w['run_id']} check {w['check']}: {w['d_score']:+} score, {w['d_tokens']:+} tokens, {w['d_heartbeats']:+} hb", "```diff", w["diff"][:500], "```"]
            if o["dead"]:
                L.append("- names that do not exist here: " + ", ".join(f"`{n}`" for n in o["dead"][:12]))
            L.append("")
        rp.write_text("\n".join(L) + "\n")
        print(f"report: {a.report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
