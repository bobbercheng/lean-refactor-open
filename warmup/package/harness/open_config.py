#!/usr/bin/env python3
"""Open-track config keys of harness/endstage.py --config (docs/open_tools_rederive.md 2.4-2.6; branch open-rederive only). A frozen config




















"""
from __future__ import annotations

import importlib, json, math, os, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KEYS = ("accept", "tunables", "tables", "entries", "census", "r5", "order", "drop_ops")
TUNABLE_MODULES = ("harness.sweep", "harness.hb_rewrite", "harness.hb_polish", "harness.gap_rules", "harness.tools.t1_compress",
                   "harness.tools.t2_schedule", "harness.tools.t3_reclose", "harness.tools.t3_suggest", "harness.tools.t4_nameless",
                   "harness.tools.hr_variant", "harness.tools.gr_rules", "harness.tools.hp_cert", "harness.batch_screen")
CENSUS_FAMILIES = ("sweep", "hr", "t1", "t2", "t3", "t4", "gr", "hp")
_STATE = {"entries": None}
_LOCK = threading.Lock()


def _endstage():
    """The running end stage module: __main__ when harness/endstage.py runs as a script (a fresh import would be a second copy whose
"""
    import sys
    m = sys.modules.get("__main__")
    if m is not None and str(getattr(m, "__file__", "")).endswith("harness/endstage.py"):
        return m
    from harness import endstage as ES
    return ES


def accept_values() -> dict:
    """The acceptance constants in force (scorer/accept and the running end stage's screen margin): the census reads them here."""
    import scorer.accept as AC
    ES = _endstage()
    return {"hb_eps": AC.HB_EPS, "min_gain": AC.MIN_GAIN, "screen_hb": ES.SCREEN_HB, "screen_frac": ES.SCREEN_FRAC}


def _num(v, low=0.0, integer=False):
    if isinstance(v, bool) or not isinstance(v, (int, float)) or not math.isfinite(v) or v < low:
        return False
    return isinstance(v, int) if integer else True


def parse(cfg: dict, path) -> dict:
    out = {}

    def bad(key, want):
        raise ValueError(f"--config {path}: {key} must be {want}, got {json.dumps(cfg.get(key.split('.')[0]))[:200]}")
    if "accept" in cfg:
        A = cfg["accept"]
        if not isinstance(A, dict) or any(k not in ("hb_eps", "min_gain", "screen_hb", "screen_frac") and not str(k).startswith("_") for k in A):
            bad("accept", "an object with hb_eps / min_gain / screen_hb / screen_frac")
        for k, integer, low in (("hb_eps", True, 1), ("min_gain", False, 0), ("screen_hb", True, 0), ("screen_frac", False, 0)):
            if k in A and not _num(A[k], low, integer):
                bad(f"accept.{k}", f"a number >= {low}" + (" (integer)" if integer else ""))
        out["accept"] = {k: v for k, v in A.items() if not str(k).startswith("_")}
    if "tunables" in cfg:
        T = cfg["tunables"]
        if not isinstance(T, dict):
            bad("tunables", "an object {module: {CONST: value}}")
        clean = {}
        for mod, d in T.items():
            if str(mod).startswith("_"):
                continue
            if mod not in TUNABLE_MODULES or not isinstance(d, dict):
                bad("tunables", f"keys among {', '.join(TUNABLE_MODULES)}")
            M = importlib.import_module(mod)
            for k, v in d.items():
                if str(k).startswith("_"):
                    continue
                cur = getattr(M, k, None)
                if isinstance(cur, dict) and isinstance(v, dict) and all(_num(x, 0, True) for x in v.values()):
                    pass
                elif isinstance(cur, bool) or not isinstance(cur, (int, float)) or not _num(v, 0, isinstance(cur, int)):
                    bad("tunables", f"numbers replacing numeric constants ({mod}.{k} is {cur!r})")
                clean.setdefault(mod, {})[k] = v
        out["tunables"] = clean
    if "tables" in cfg:
        t = cfg["tables"]
        if t != "measure_range" and not (isinstance(t, str) and (ROOT / t).is_file()):
            bad("tables", '"measure_range" or the path (relative to the worktree) of a shipped tables file')
        out["tables"] = t
    if "entries" in cfg:
        E = cfg["entries"]
        if not (isinstance(E, dict) and all(isinstance(v, list) and all(isinstance(x, str) for x in v) for k, v in E.items() if not str(k).startswith("_"))):
            bad("entries", "an object {op id: [entry, ...]}")
        out["entries"] = {k: list(v) for k, v in E.items() if not str(k).startswith("_")}
    if "census" in cfg:
        C = cfg["census"]
        B = (C or {}).get("budgets") if isinstance(C, dict) else None
        if not (isinstance(B, dict) and set(k for k in B if not k.startswith("_")) == {"seed", "final"}
                and all(isinstance(B[g], dict) and all(f in CENSUS_FAMILIES and _num(s, 1) for f, s in B[g].items() if not f.startswith("_"))
                        for g in ("seed", "final"))):
            bad("census", f'{{"budgets": {{"seed": {{family: seconds}}, "final": {{...}}}}}} over {", ".join(CENSUS_FAMILIES)}')
        pools = C.get("pools") or {}
        if not (isinstance(pools, dict) and all(a in CENSUS_FAMILIES and b in CENSUS_FAMILIES for a, b in pools.items() if not a.startswith("_"))):
            bad("census.pools", "an object {family: family whose budget it shares}")
        ns = C.get("probe_hb_samples", 2)
        if not _num(ns, 0, True):
            bad("census.probe_hb_samples", "an integer >= 0")
        out["census"] = {"budgets": {g: {f: s for f, s in B[g].items() if not f.startswith("_")} for g in ("seed", "final")},
                         "pools": {a: b for a, b in pools.items() if not a.startswith("_")}, "probe_hb_samples": ns}
    if "order" in cfg:
        o = cfg["order"]
        if not (isinstance(o, list) and all(isinstance(x, str) and x in CENSUS_FAMILIES for x in o)):
            bad("order", f"a list of families among {', '.join(CENSUS_FAMILIES)}")
        out["order"] = list(dict.fromkeys(o))
    if "drop_ops" in cfg:
        d = cfg["drop_ops"]
        if not (isinstance(d, list) and all(isinstance(x, str) and ":" in x for x in d)):
            bad("drop_ops", "a list of op ids (\"family:op\")")
        out["drop_ops"] = sorted(set(d))
    if "r5" in cfg:
        R = cfg["r5"]
        if not (isinstance(R, dict) and isinstance(R.get("env", "LRA_END_STAGE_SECONDS"), str) and _num(R.get("sweep_share"), 0)
                and 0 < R["sweep_share"] < 1):
            bad("r5", '{"env": name, "sweep_share": number in (0, 1)}')
        out["r5"] = {"env": R.get("env", "LRA_END_STAGE_SECONDS"), "sweep_share": float(R["sweep_share"])}
    return out


def apply(vals: dict | None) -> dict:
    """Set what `vals` (parse()) asks at run start; the record of the values replaced (for end_config.json)."""
    rec: dict = {}
    vals = vals or {}
    if vals.get("tables"):
        import sys
        sys.path.insert(0, str(ROOT))
        from probe.open_rederive import opentables as OT
        if vals["tables"] == "measure_range":
            rec["tables"] = OT.record_of(OT.apply())
        else:
            rec["tables"] = OT.apply_shipped(ROOT / vals["tables"])
    if vals.get("accept"):
        import scorer.accept as AC
        ES = _endstage()
        A = vals["accept"]
        rec["accept"] = {"old": {"hb_eps": AC.HB_EPS, "min_gain": AC.MIN_GAIN, "screen_hb": ES.SCREEN_HB, "screen_frac": ES.SCREEN_FRAC}, "new": dict(A)}
        if "hb_eps" in A:
            AC.HB_EPS = int(A["hb_eps"])
        if "min_gain" in A:
            AC.MIN_GAIN = float(A["min_gain"])
        ES.SCREEN_HB = int(A.get("screen_hb", 2 * AC.HB_EPS))
        if "screen_frac" in A:
            ES.SCREEN_FRAC = float(A["screen_frac"])
    if vals.get("tunables"):
        rec["tunables"] = {}
        for mod, d in vals["tunables"].items():
            M = importlib.import_module(mod)
            for k, v in d.items():
                old = getattr(M, k)
                setattr(M, k, dict(old, **v) if isinstance(old, dict) else type(old)(v))
                rec["tunables"].setdefault(mod, {})[k] = {"old": old, "new": getattr(M, k)}
        _refresh_derived()
    with _LOCK:
        _STATE["entries"] = dict(vals["entries"]) if vals.get("entries") else None
        _STATE["drop"] = frozenset(vals.get("drop_ops") or ())
    ES = _endstage()
    ES._ENTRY_FILTER = filter_entries if (vals.get("entries") or vals.get("drop_ops")) else None
    if vals.get("order"):
        ES._FAMILY_ORDER = tuple(vals["order"])
        rec["order"] = list(vals["order"])
    if vals.get("drop_ops"):
        rec["drop_ops"] = len(vals["drop_ops"])
    if vals.get("entries"):
        rec["entries"] = {k: len(v) for k, v in vals["entries"].items()}
    return rec


def _refresh_derived() -> None:
    """Module values computed at import from a tunable (hb_rewrite's specialize map from SPEC_CAP)."""
    import sys
    HR = sys.modules.get("harness.hb_rewrite")
    if HR is not None:
        HR.SPECIALIZE = HR.specialize_map(HR._load_table(HR.SPEC_TABLE), cap=HR.SPEC_CAP)
        HR.SPEC_RE = HR.spec_regex(HR.SPECIALIZE)


def filter_entries(fam: str, items: list[dict]) -> tuple[list[dict], int]:
    """(kept items, dropped count): items of a table-driven op whose entry is not in the config's "entries" for that op are dropped."""
    with _LOCK:
        E = _STATE["entries"] or {}
        D = _STATE.get("drop") or frozenset()
    if not E and not D:
        return items, 0
    import sys
    sys.path.insert(0, str(ROOT))
    from probe.open_rederive import opentables as OT
    from probe.open_rederive.ops import canon
    kept, dropped = [], 0
    for it in items:
        fop = canon(f"{fam}:{it.get('op')}" if it.get("op") and not str(it.get("op")).startswith(fam + ":") else (it.get("op") or fam))
        if fop in D:
            dropped += 1
            continue
        if fop in E:
            note = it.get("full") or it.get("note") or it.get("label") or ""
            if it.get("op") and note.startswith(str(it["op"]) + ": "):                                              
                note = note[len(str(it["op"])) + 2:]
            ent = OT.entry_of(fop, note, it.get("closer"))
            if ent is not None and ent not in E[fop]:
                dropped += 1
                continue
        kept.append(it)
    return kept, dropped


def r5_budget(vals: dict | None, jobs: int, rows_left: int, started: float, now: float) -> dict | None:
    """{"max_seconds", "tools_max_seconds"} of the next row under "r5", or None (no r5, or the env variable unset)."""
    R = (vals or {}).get("r5")
    if not R:
        return None
    try:
        total = float(os.environ[R["env"]])
    except (KeyError, ValueError):
        return None
    left = max(0.0, total - (now - started))
                                                                                                                                          
                                                                                                                                         
                                                                                                                                          
    allow = min(left, left * max(1, int(jobs)) / max(1, int(rows_left)))
    return {"max_seconds": max(1.0, allow * R["sweep_share"]), "tools_max_seconds": max(1.0, allow * (1.0 - R["sweep_share"]))}
