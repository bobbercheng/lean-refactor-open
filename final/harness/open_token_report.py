#!/usr/bin/env python3
"""Per-run token report of the open package's agent stage (2026-10-28, docs/open_package_audit.md section P, P4). The closed line's



















"""
from __future__ import annotations

import argparse, collections, gzip, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
AUTO_CHECK = "[auto lean_check of candidate.lean — do not check it again]\n"                                                          
EVENTS = ("budget_forcing", "nothink_rescue", "length_continuation", "junk_abort", "junk_tool_call", "junk_text", "runaway_tool_call",
          "api_retry", "api_error", "connect_retry", "rate_limit")


def _open(f: Path):
    return gzip.open(f, "rt", errors="replace") if str(f).endswith(".gz") else open(f, errors="replace")


def json_part(txt: str) -> str | None:
    """The JSON object a tool result carries: the whole result, or the part after a write_file's auto-check line; None otherwise."""
    if AUTO_CHECK in txt:
        txt = txt.split(AUTO_CHECK, 1)[1]
    return txt if txt[:1] in "{[" else None


def compact(obj) -> str:
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))


def sessions_of(f: Path) -> list:
    """A trajectory file's records split into sessions (agent.py appends a resumed run's session to the same gzip: one header each)."""
    segs: list = []
    with _open(f) as fh:
        for l in fh:
            try:
                d = json.loads(l)
            except ValueError:
                continue                                          
            if not isinstance(d, dict):
                continue
            if d.get("type") == "header" or not segs:
                segs.append([])
            segs[-1].append(d)
    return segs


def file_stats(f: Path, c: collections.Counter) -> None:
    """Add one trajectory file's sessions to `c` (keys: see derive)."""
    for recs in sessions_of(f):
        session_stats(recs, c)


def session_stats(recs: list, c: collections.Counter) -> None:
    try:
        from llm.junk import junk_reason
    except ImportError:                                                                            
        junk_reason = lambda *_a, **_k: None               
    names: dict = {}
    c["sessions"] += 1
    later = [0] * (len(recs) + 1)                                                                                                 
    for i in range(len(recs) - 1, -1, -1):
        later[i] = later[i + 1] + (recs[i].get("type") == "turn")
    for i, d in enumerate(recs):
        t = d.get("type")
        if t in EVENTS:
            c["ev:" + t] += 1
            if t == "runaway_tool_call" and d.get("degenerate"):
                c["ev:runaway_degenerate"] += 1
        if t == "message" and isinstance(d.get("content"), list):
            role = d.get("role")
            if role == "assistant":
                c["assistant_messages"] += 1
            for x in d["content"]:
                if not isinstance(x, dict):
                    continue
                if role == "assistant":
                    if x.get("type") == "tool_use":
                        names[x.get("id")] = x.get("name"); c["tool_calls"] += 1; c["calls:" + str(x.get("name"))] += 1
                        inp = x.get("input")
                        if isinstance(inp, dict) and "_dropped" not in inp and junk_reason(json.dumps(inp, ensure_ascii=False)):
                            c["scan:junk_tool_call"] += 1
                    elif x.get("type") == "text" and x.get("text") and junk_reason(x["text"]):
                        c["scan:junk_text"] += 1
                    elif x.get("type") == "thinking" and x.get("thinking") and junk_reason(x["thinking"], max_chars=10 ** 9):
                        c["scan:degenerate_thinking"] += 1
                elif x.get("type") == "tool_result":
                    raw = x.get("content")
                    txt = raw if isinstance(raw, str) else " ".join(y.get("text", "") for y in raw if isinstance(y, dict)) if isinstance(raw, list) else ""
                    nm = str(names.get(x.get("tool_use_id"), "?"))
                    c["tool_chars"] += len(txt); c["tool_chars:" + nm] += len(txt)
                    js, alt = json_part(txt), len(txt)
                    if js is not None:
                        try:
                            obj = json.loads(js)
                        except ValueError:
                            obj = None                                                         
                        if obj is not None:
                            cj = compact(obj)
                            c["json_results"] += 1; c["json_chars"] += len(js); c["json_chars_if_compact"] += len(cj)
                            c["json_compact"] += js == cj; c["json_u_escapes"] += js.count("\\u")
                            c["json_chars:" + nm] += len(js); c["json_chars_if_compact:" + nm] += len(cj)
                            alt = len(txt) - len(js) + len(cj)
                    c["tool_prefill_chars"] += len(txt) * later[i]; c["tool_prefill_chars_if_compact"] += alt * later[i]
        if t == "turn":
            inp, out = int(d.get("input_tokens") or 0), int(d.get("output_tokens") or 0)
            c["turns"] += 1; c["input_tokens"] += inp; c["output_tokens"] += out
            c["reasoning_tokens"] += int(d.get("reasoning_tokens") or 0); c["model_seconds"] += float(d.get("seconds") or 0)
            if d.get("turn") == 0:
                c["opening_input_tokens"] += inp
            cap = d.get("max_tokens")
            if str(d.get("stop")) == "max_tokens" or (cap and out >= int(cap)):
                c["turns_at_cap"] += 1; c["output_tokens_at_cap"] += out


def derive(c: collections.Counter) -> dict:
    """The counters plus per-turn means and shares."""
    t = max(1, c["turns"]); out = dict(sorted(c.items()))
    out.update({
        "input_per_turn": round(c["input_tokens"] / t), "output_per_turn": round(c["output_tokens"] / t),
        "turns_per_session": round(c["turns"] / max(1, c["sessions"]), 1),
        "opening_input_share": round(c["opening_input_tokens"] / max(1, c["input_tokens"]), 4),
        "at_cap_turn_share": round(c["turns_at_cap"] / t, 4), "at_cap_output_share": round(c["output_tokens_at_cap"] / max(1, c["output_tokens"]), 4),
        "junk_events": sum(c["ev:" + k] for k in ("junk_abort", "junk_tool_call", "junk_text", "runaway_degenerate")),
        "junk_scan": c["scan:junk_tool_call"] + c["scan:junk_text"] + c["scan:degenerate_thinking"],
        "json_compact_share": round(c["json_compact"] / max(1, c["json_results"]), 4),
        "json_chars_change_if_compact": round(c["json_chars_if_compact"] / max(1, c["json_chars"]) - 1, 4) if c["json_chars"] else 0.0,
        "tool_prefill_chars_change_if_compact": (round(c["tool_prefill_chars_if_compact"] / max(1, c["tool_prefill_chars"]) - 1, 4)
                                                 if c["tool_prefill_chars"] else 0.0),
    })
    return out


def report(groups: dict) -> dict:
    """{label: [trajectory files]} -> {"groups": {label: derive(...)}, "all": derive(...)}."""
    res, tot = {}, collections.Counter()
    for label, files in groups.items():
        c = collections.Counter()
        for f in files:
            file_stats(Path(f), c)
        res[label] = derive(c); tot.update(c)
    return {"groups": res, "all": derive(tot)}


def traj_files(run_dir: Path) -> list:
    return sorted((Path(run_dir) / "trajectories").glob("*.jsonl*"))


def report_for_out(out: Path, runs_root: Path) -> dict:
    """A package run: one group per session index k (agent_sessions.jsonl), trajectories under runs_root/<run id>/."""
    groups: dict = {}
    p = Path(out) / "agent_sessions.jsonl"
    for l in (p.read_text().splitlines() if p.exists() else []):
        try:
            r = json.loads(l)
        except ValueError:
            continue
        if isinstance(r, dict) and r.get("run_id"):
            groups.setdefault(f"k{int(r.get('k') or 0)}", []).extend(traj_files(Path(runs_root) / r["run_id"]))
    rep = report(dict(sorted(groups.items(), key=lambda kv: int(kv[0][1:]))))
    rep["source"] = {"out": str(out), "runs_root": str(runs_root)}
    return rep


def one_line(rep: dict) -> str:
    a = rep["all"]
    return (f"{a.get('sessions', 0)} sessions, {a.get('turns', 0)} turns; input {a['input_per_turn']} / output {a['output_per_turn']} tokens "
            f"per turn (opening {100 * a['opening_input_share']:.1f}% of input); at the output cap {100 * a['at_cap_turn_share']:.1f}% of "
            f"turns, {100 * a['at_cap_output_share']:.1f}% of output; junk events {a['junk_events']}, junk scan {a['junk_scan']}; budget "
            f"forcing {a.get('ev:budget_forcing', 0)}; connect retries {a.get('ev:connect_retry', 0)}, api retries {a.get('ev:api_retry', 0)}; "
            f"JSON tool results {a.get('json_results', 0)} ({100 * a['json_compact_share']:.0f}% compact, chars "
            f"{100 * a['json_chars_change_if_compact']:+.1f}% if all were)")


def table(rep: dict) -> str:
    cols = ("sessions", "turns", "input_per_turn", "output_per_turn", "opening_input_share", "at_cap_turn_share", "at_cap_output_share",
            "junk_events", "junk_scan", "ev:budget_forcing", "ev:connect_retry", "json_compact_share", "json_chars_change_if_compact",
            "tool_prefill_chars_change_if_compact")
    rows = [("group",) + tuple(c.replace("ev:", "") for c in cols)]
    for k, g in list(rep["groups"].items()) + [("ALL", rep["all"])]:
        rows.append((k,) + tuple(str(g.get(c, 0)) for c in cols))
    w = [max(len(r[i]) for r in rows) for i in range(len(rows[0]))]
    return "\n".join("  ".join(x.rjust(w[i]) for i, x in enumerate(r)) for r in rows)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--out", help="a package run's output directory (agent_sessions.jsonl)")
    g.add_argument("--runs", nargs="+", help="agent.py run directories (probe/runs/<run id>)")
    ap.add_argument("--runs-root", default=str(ROOT / "probe/runs"), help="with --out: where the sessions' run directories are")
    ap.add_argument("--json", help="write the report here")
    a = ap.parse_args(argv)
    rep = report_for_out(Path(a.out), Path(a.runs_root)) if a.out else report({Path(r).name: traj_files(Path(r)) for r in a.runs})
    print(table(rep)); print(one_line(rep))
    if a.json:
        Path(a.json).write_text(json.dumps(rep, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
