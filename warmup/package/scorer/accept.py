"""Paired, unrounded acceptance rule (B62b/B62c; docs/scaffold_panel.md "Agreed" and "Rulings").










"""
from __future__ import annotations

MIN_GAIN = 0.005                   
SMALL = 0.01                                                                                                                    
HB_EPS = 3                                                                                                 
SIGNAL_GAIN = 0.05                                      


def exact_score(L: float, H: float, Z: float) -> float:
    """The official per-problem score before rounding: mean of the length, heartbeat and compatibility percentages."""
    return (L + H + Z) / 3.0


def decide(inc: dict, cand: dict) -> tuple[bool, str]:
    """inc, cand: {"score": exact score, "tokens": int, "heartbeats": int, "Z": percent}. Returns (bank it, reason)."""
    if cand.get("score") is None or inc.get("score") is None:
        return False, "no score"
    if float(cand.get("Z", 100.0)) < float(inc.get("Z", 100.0)):
        return False, "compiles on fewer toolchains"
    d = float(cand["score"]) - float(inc["score"])
    dt = int(inc.get("tokens") or 0) - int(cand.get("tokens") or 0)
    dh = int(inc.get("heartbeats") or 0) - int(cand.get("heartbeats") or 0)
    if float(cand.get("Z", 100.0)) > float(inc.get("Z", 100.0)) and d > 0:
        return True, f"{d:+.4f} (compiles on more toolchains)"
    if not (dt >= 1 or dh >= HB_EPS):
        return False, f"{d:+.4f}: saves no token and fewer than {HB_EPS} heartbeats (within the meter's spread)"
    if d > 0 and dt >= 0 and dh >= 0:
        return True, f"dominates ({dt:+d} tokens, {dh:+d} heartbeats saved, {d:+.4f})"
    if d >= MIN_GAIN:
        return True, f"{d:+.4f} ({dt:+d} tokens, {dh:+d} heartbeats saved)"
    return False, f"{d:+.4f} is below the bar (+{MIN_GAIN})"
