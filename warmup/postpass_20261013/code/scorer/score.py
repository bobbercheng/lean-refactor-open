"""Official scoring formulas (from leaderboard.py, verified 2026-10-06)."""
from __future__ import annotations


def len_pct(orig_len: int, new_len: int) -> float:
    return ((orig_len - new_len) / orig_len * 100.0) if orig_len > 0 else 0.0


def hb_pct(orig_hb: int | None, new_hb: int | None) -> float:
    return ((orig_hb - new_hb) / orig_hb * 100.0) if (orig_hb and new_hb is not None) else 0.0


def compat_pct(compat: dict[str, bool]) -> float:
    return (sum(1 for v in compat.values() if v) / len(compat) * 100.0) if compat else 100.0


def problem_score(compiled: bool, L: float, H: float, Z: float) -> float:
    if not compiled:
        return 0.0
    return round((L + H + Z) / 3.0, 2)


def aggregate(per_problem: dict[str, float], all_names: list[str]) -> float:
    """Mean over ALL benchmark problems; missing problems contribute 0."""
    return round(sum(per_problem.get(n, 0.0) for n in all_names) / len(all_names), 2) if all_names else 0.0


import json as _json
from pathlib import Path as _Path

_LOCAL_REF = None


def local_reference_heartbeats(name: str) -> int | None:
    """Reference heartbeats measured with OUR counter (scorer/calibrate.py), so
    the candidate/reference ratio cancels the counter's constant offset."""
    global _LOCAL_REF
    if _LOCAL_REF is None:
        f = _Path(__file__).resolve().parents[1] / "data/reference_heartbeats_local.json"
        _LOCAL_REF = _json.loads(f.read_text()) if f.exists() else {}
    e = _LOCAL_REF.get(name) or {}
    return e.get("heartbeats_local")


def hb_pct_local(name: str, new_hb: int | None, official_ref: int | None) -> float:
    """Heartbeat reduction % as the official scorer will compute it, predicted
    via the local ratio: (1 - new/ref_local) * 100. Falls back to the official
    reference when no local measurement exists."""
    ref = local_reference_heartbeats(name) or official_ref
    return ((ref - new_hb) / ref * 100.0) if (ref and new_hb is not None) else 0.0
