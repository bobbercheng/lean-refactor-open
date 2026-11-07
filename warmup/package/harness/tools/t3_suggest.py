#!/usr/bin/env python3
"""T3 goal-aware closers (round R3, opt-in): ask Lean which tactic closes the goal left at each of T3's top spans, then let T3 propose the








































































"""
from __future__ import annotations

import argparse, hashlib, json, math, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.batch_screen import SUFFIX as BATCH_SUFFIX                                                         
from scorer.tokenize import count_tokens              

PROBE_MATHLIB = "hint"                          
PROBE_CORE = "try?"                              
PROBE_RULE = ("probe tactic: Mathlib's `hint` when the row imports Mathlib (t3_reclose._scope == 'mathlib'), else Lean core's `try?`; "
              "a probe whose copies all fail with 'unknown tactic' at the probe is redone with `try?`; opt-in modes: try?, hint, both")
PROBE_K = 20                                                                                   
PROBE_EXTRA_S = 20                                                                                                    
PROBE_HB_SEARCH = 20000                                                                                                             
PROBE_DEPTH = 1                                                                
PROBE_MAX_FILES = 2                                                                                                               
TARGET_S = 600                                                                                        
UNKNOWN_TACTIC = "unknown tactic"
REMAINING = "Remaining subgoals:"

_HEAD = re.compile(r"^\s*Try (?:this|these):[ \t]*(.*)$")
_ITEM = re.compile(r"^(\s*)(?:\[apply\]|•)[ \t]?(.*)$")
_APPLY = re.compile(r"^\[apply\][ \t]?")
_PARTY = re.compile("^\U0001F389️?[ \t]*")
_SORRY = re.compile(r"(?<![\w.'])(?:sorry|admit)(?![\w'])")
_SEARCH = re.compile(r"[\w']\?(?![\w'])")
_HB_OUT = re.compile(r"maximum number of heartbeats|deterministic\) timeout|\(kernel\) deterministic timeout")                     
_INTERNAL = re.compile(r"(?:^|(?<=[^\w'.])|(?<=\.))_[A-Za-z0-9]")                                                                                                                                                                          


def proof_key(proof: str) -> str:
    """The key T3 checks ctx["suggestions_for"] against (sha256 of the stripped proof, 16 hex digits; harness/endstage.sha)."""
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def probe_tactic(scope: str) -> str:
    """PROBE_RULE: `hint` for a Mathlib scope, `try?` otherwise."""
    return PROBE_MATHLIB if scope == "mathlib" else PROBE_CORE


MODES = ("rule", "try?", "hint", "both")


def probe_tactics(scope: str, mode: str | None = "rule") -> tuple[str, ...]:
    """The probe tactics of a row of T3 scope `scope` under `mode` (module docstring, "probe")."""
    if mode in (None, "rule", True):
        return (probe_tactic(scope),)
    if mode == "both":
        return (PROBE_MATHLIB, PROBE_CORE) if scope == "mathlib" else (PROBE_CORE,)
    if mode in (PROBE_CORE, PROBE_MATHLIB):
        return (mode,)
    raise ValueError(f"unknown probe mode {mode!r} (known: {', '.join(MODES)})")


def probe_hb_cap(heartbeats) -> int:
    """`maxHeartbeats` of a probe copy (thousands): the incumbent's heartbeats + PROBE_HB_SEARCH."""
    try:
        h = int(heartbeats or 0)
    except (TypeError, ValueError):
        h = 0
    return max(0, h) + PROBE_HB_SEARCH


                                                                                                                                     
def _depth0_newline(text: str) -> bool:
    depth = 0
    for ch in text:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "\n" and depth <= 0:
            return True
    return False


def _why_dropped(text: str, probe: str | None) -> str | None:
    if not text:
        return "empty"
    if "--" in text or "/-" in text:
        return "comment"
    if "#" in text:
        return "pin_local"
    if BATCH_SUFFIX in text:
        return "batch_copy"
    if _INTERNAL.search(text):
        return "internal"
    if "✝" in text:
        return "inaccessible"
    if _SORRY.search(text):
        return "sorry"
    if _SEARCH.search(text):
        return "search"
    if probe is not None and text == probe:
        return "probe"
    return None


def parse_message(data, probe: str | None = None) -> list[dict]:
    """The suggestions of one Lean message: [{"text", "kept", "why"}] in Lean's order ("text": whitespace-collapsed for a one-line

"""
    lines = str(data or "").split("\n")
    m = _HEAD.match(lines[0]) if lines else None
    if not m:
        return []
    items: list[dict] = []
    cur = None
    if m.group(1).strip():                                                 
        cur = {"lines": [_APPLY.sub("", m.group(1).strip())], "closes": True, "done": False}
        items.append(cur)
    for ln in lines[1:]:
        im = _ITEM.match(ln)
        if im:
            cur = {"lines": [im.group(2)], "closes": True, "done": False}
            items.append(cur)
            continue
        if cur is None:
            continue
        if ln.strip() == REMAINING:
            cur["closes"], cur["done"] = False, True
            continue
        if not cur["done"] and ln.strip():
            cur["lines"].append(ln)
    out = []
    for it in items:
        first = _PARTY.sub("", it["lines"][0].strip())
        raw = "\n".join([first] + it["lines"][1:]).strip()
        if not it["closes"]:
            out.append({"text": " ".join(raw.split()), "kept": False, "why": "progress"})
            continue
        if _depth0_newline(raw):
            out.append({"text": raw, "kept": False, "why": "structured"})
            continue
        text = " ".join(raw.split())
        why = _why_dropped(text, probe)
        out.append({"text": text, "kept": why is None, "why": why})
    return out


def _line_of(m: dict) -> int | None:
    return m.get("decl_line") if m.get("decl_line") is not None else (m.get("pos") or {}).get("line")


def suggestions_at(messages, line: int, probe: str | None = None) -> tuple[list[str], dict]:
    """(kept suggestions, info) from the messages of one copy at `line` (each message's "decl_line", else its "pos" line): the
"""
    kept, seen, info = [], set(), {"dropped": {}, "unknown_tactic": False, "messages": 0}
    for m in messages or []:
        if _line_of(m) != line:
            continue
        data = str(m.get("data", ""))
        if m.get("severity") == "error" and data.strip().startswith(UNKNOWN_TACTIC):
            info["unknown_tactic"] = True
        if m.get("severity") != "information":
            continue
        got = parse_message(data, probe)
        if got:
            info["messages"] += 1
        for s in got:
            if not s["kept"]:
                info["dropped"][s["why"]] = info["dropped"].get(s["why"], 0) + 1
            elif s["text"] not in seen:
                seen.add(s["text"])
                kept.append(s["text"])
    return kept, info


                                                                                                                                     
def as_example(statement: str, proof: str | None = None) -> str | None:
    """`statement` with its last declaration written as an `example` (module docstring, "anonymous"), or None when that is not done.
"""
    from harness.batch_screen import _DECL_KW, _ID_AFTER, _ID_BEFORE, declared, mask
    m = mask(statement)
    kws = list(_DECL_KW.finditer(m))
    decls = declared(statement)
    if not kws or not decls or len(kws) != len(decls):
        return None
    k, (kw, name, pos) = kws[-1], decls[-1]
    if kw not in ("theorem", "lemma", "def", "abbrev") or not name:
        return None
    gap = statement[k.end(1):pos]
    end = pos + len(name)
    if gap.strip(" \t") or statement[end:end + 2] == ".{" or statement[pos:end] != name:
        return None
    if "." in name and not name.startswith("«"):                                                                              
        return None
    if proof is not None and proof.startswith(statement):
        body = mask(proof)[len(statement):]
        if re.search(_ID_BEFORE + re.escape(name) + _ID_AFTER, body):
            return None
    head = statement[:k.start(1)]
    pm = re.search(r"(?<![\w.'])protected[ \t]+$", head)
    if pm:
        head = head[:pm.start()]
    return head + "example" + statement[end:]


def _span_key(sp) -> tuple[int, int] | None:
    try:
        if isinstance(sp, dict):
            return int(sp["start"]), int(sp["end"])
        a, b = sp
        return int(a), int(b)
    except (KeyError, TypeError, ValueError):
        return None


def probe_text(proof: str, key: tuple[int, int], tactic: str) -> str:
    return proof[:key[0]] + tactic + proof[key[1]:]


def suggest(proof: str, statement: str, spans, compile_batch, *, tactic=PROBE_CORE, fallback: str | None = PROBE_CORE,
            max_spans: int | None = None, stats: dict | None = None, log=None, require_clean: bool = True) -> dict:
    """{(start, end): [tactic, ...]} (module docstring, "result") for `spans` (T3 span dicts with "start" / "end", or (start, end) pairs)






"""
    st = stats if stats is not None else {}
    log = log or (lambda m: None)
    keys = []
    for sp in (spans or []) if proof.startswith(statement) else []:
        k = _span_key(sp)
        if k and len(statement) <= k[0] < k[1] <= len(proof) and k not in keys:
            keys.append(k)
    if max_spans is not None:
        keys = keys[:max(0, int(max_spans))]
    st.setdefault("probes", 0)
    st.setdefault("judged", 0)
    st.setdefault("dropped", {})
    for c in ("spans_with", "suggestions"):
        st.setdefault(c, 0)
    if not keys:
        st.setdefault("tactic", tactic)
        return {}
    t0 = time.time()

    tacs = (tactic,) if isinstance(tactic, str) else tuple(dict.fromkeys(tactic))
    by = st.setdefault("by_tactic", {})

    def run(tac):
        """One tactic over every span, in one compile_batch call (its own files): ({span: [kept]}, judged, unknown)."""
        B = by.setdefault(tac, {})
        for c in ("probes", "judged", "unknown", "hb_out", "timeout", "crash", "skipped", "unbuildable", "spans_with", "suggestions"):
            B.setdefault(c, 0)
        texts = [probe_text(proof, k, tac) for k in keys]
        t1 = time.time()
        got = compile_batch(texts)
        B["seconds"] = round(B.get("seconds", 0.0) + time.time() - t1, 1)
        why = dict(getattr(got, "why", None) or {})
        got = list(got or []) + [None] * (len(texts) - len(got or []))
        st["probes"] += len(texts)
        B["probes"] += len(texts)
        merged, judged, unknown = {}, 0, 0
        for i, (k, text, msgs) in enumerate(zip(keys, texts, got)):
            if msgs is None:
                w = why.get(i, "timeout")
                B[w] = B.get(w, 0) + 1
                continue
            judged += 1
            B["hb_out"] += any(m.get("severity") == "error" and _HB_OUT.search(str(m.get("data", ""))) for m in msgs)
            kept, info = suggestions_at(msgs, text[:k[0]].count("\n") + 1, tac)
            unknown += bool(info["unknown_tactic"])
            for w, n in info["dropped"].items():
                st["dropped"][w] = st["dropped"].get(w, 0) + n
            if kept and require_clean and any(m.get("severity") == "error" for m in msgs):
                st["dropped"]["copy_error"] = st["dropped"].get("copy_error", 0) + len(kept)
                kept = []
            if kept:
                merged.setdefault(k, []).extend(t for t in kept if t not in merged.get(k, []))
        st["judged"] += judged
        B["judged"] += judged
        B["unknown"] += unknown
        B["spans_with"] += len(merged)
        B["suggestions"] += sum(len(v) for v in merged.values())
        return merged, judged, unknown

    merged: dict = {}
    for tac in tacs:
        got, judged, unknown = run(tac)
        if fallback and len(tacs) == 1 and fallback != tac and judged and unknown == judged:
            log(f"t3 suggest: `{tac}` is unknown on this row; probing again with `{fallback}`")
            st["fallback"] = fallback
            got, judged, unknown = run(fallback)
        for k in keys:                                                         
            for t in got.get(k, []):
                if t not in merged.setdefault(k, []):
                    merged[k].append(t)
    res = {k: sorted(v, key=lambda s: (count_tokens(s), v.index(s))) for k, v in merged.items() if v}
    st["tactic"] = "+".join(tacs)
    st["spans_with"] += len(res)
    st["suggestions"] += sum(len(v) for v in res.values())
    st["seconds"] = round(st.get("seconds", 0.0) + time.time() - t0, 1)
    return res


class _Judged(list):
    """compile_batch's result: a list (None for a copy that was not judged) with "why" {index: reason} for those copies."""

    def __init__(self, items=()):
        super().__init__(items)
        self.why: dict = {}


def batch_compiler(statement: str, compile_fn, layout, *, hb_cap: int | None = None, compile_s: float | None = None, timeout: int = 900,
                   k: int = PROBE_K, depth: int = PROBE_DEPTH, need=None, charge=None, stats: dict | None = None, log=None,
                   anonymous: bool = True, max_files: int | None = PROBE_MAX_FILES):
    """compile_batch for suggest() on harness/batch_screen.py's file layout (module docstring, "batch"). compile_fn(body, copies, layout,




"""
    from harness.batch_screen import build
    st = stats if stats is not None else {}
    log = log or (lambda m: None)
    cs = float(compile_s) if isinstance(compile_s, (int, float)) and compile_s > 0 else 60.0
    kb = max(1, min(int(k), int(TARGET_S // (cs + PROBE_EXTRA_S))))

    def _anon(t: str) -> tuple[str, str]:                                                                   
        if anonymous and t.startswith(statement):
            ex = as_example(statement, t)
            if ex is not None:
                return ex + t[len(statement):], ex
        return t, statement

    def compile_batch(texts: list[str]) -> list:
        out = _Judged([None] * len(texts))
        files = [0]
        forms = [_anon(t) for t in texts]
        st["anonymous"] = st.get("anonymous", 0) + sum(1 for _, s_ in forms if s_ != statement)
        groups: dict = {}
        for i, (_, s_) in enumerate(forms):
            groups.setdefault(s_, []).append(i)
        queue = [(g[i:i + kb], 0) for g in groups.values() for i in range(0, len(g), kb)]
        while queue:
            idx, d = queue.pop(0)
            body, copies, spans = build([forms[i][0] for i in idx], forms[idx[0]][1], layout, hb_cap)
            if d == 0 and any(sp is None for sp in spans):                                                            
                st["unbuildable"] = st.get("unbuildable", 0) + sum(sp is None for sp in spans)
            for i, sp in zip(idx, spans):
                if sp is None:
                    out.why[i] = "unbuildable"
            if all(sp is None for sp in spans):
                continue
            if max_files is not None and files[0] >= int(max_files):
                st["copies_skipped"] = st.get("copies_skipped", 0) + sum(sp is not None for sp in spans)
                out.why.update({i: "skipped" for i, sp in zip(idx, spans) if sp is not None})
                continue
            if need:
                need(1)
            files[0] += 1
            to = int(max(1, min(int(timeout), math.ceil(cs + len(idx) * (cs + PROBE_EXTRA_S)) + 30)))
            t0 = time.time()
            res, n = compile_fn(body, copies, layout, to)
            if charge:
                charge(int(n))
            st["batches"] = st.get("batches", 0) + 1
            st["compiles"] = st.get("compiles", 0) + int(n)
            st["batch_seconds"] = round(st.get("batch_seconds", 0.0) + time.time() - t0, 1)
            msgs = list(getattr(res, "messages", None) or [])
            if getattr(res, "timed_out", False) or (not msgs and not getattr(res, "ok", False)):
                kind = "timeout" if getattr(res, "timed_out", False) else "crash"
                st[kind + "s"] = st.get(kind + "s", 0) + 1
                if d < depth and len(idx) > 1:
                    h = (len(idx) + 1) // 2
                    queue[:0] = [(idx[:h], d + 1), (idx[h:], d + 1)]
                    log(f"t3 suggest: a probe file of {len(idx)} {kind}; halved")
                else:
                    out.why.update({i: kind for i, sp in zip(idx, spans) if sp is not None})
                continue
            for j, sp in enumerate(spans):
                if sp is None:
                    continue
                s, mk = sp
                text = forms[idx[j]][0].strip()
                first = (mk - 2) - text.count("\n")                                                                       
                out[idx[j]] = [dict(m, decl_line=((m.get("pos") or {}).get("line") or 0) - first + 1) for m in msgs
                               if s <= ((m.get("pos") or {}).get("line") or 0) < mk]
        return out
    return compile_batch


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--messages", required=True, help="a `lean --json` output (one JSON message per line)")
    ap.add_argument("--line", type=int, required=True)
    ap.add_argument("--probe", default=None)
    a = ap.parse_args(argv)
    msgs = [json.loads(l) for l in Path(a.messages).read_text().splitlines() if l.startswith("{")]
    kept, info = suggestions_at(msgs, a.line, a.probe)
    print(json.dumps({"kept": kept, **info}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
