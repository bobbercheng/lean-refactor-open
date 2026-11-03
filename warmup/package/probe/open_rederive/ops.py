#!/usr/bin/env python3
"""The 94 op ids of the open-track re-derivation (docs/open_tools_rederive.md 1a) and their canonical spelling.







"""
from __future__ import annotations

FAMILY_MODULES = {"sweep": "harness/sweep.py", "hr": "harness/hb_rewrite.py", "t1": "harness/tools/t1_compress.py",
                  "t2": "harness/tools/t2_schedule.py", "t3": "harness/tools/t3_reclose.py", "t4": "harness/tools/t4_nameless.py",
                  "gr": "harness/gap_rules.py", "hp": "harness/hb_polish.py"}
HP_OPS = ("hp:cert", "hp:prune")


def canon(fop: str) -> str:
    f = str(fop or "")
    return f[len("sweep:"):] if f.startswith("sweep:hr:") else f


def family_of(op: str) -> str:
    return op.split(":", 1)[0]


def all_ops() -> list[str]:
    """Every op id, family by family in the order of FAMILY_MODULES (94)."""
    from harness import sweep as SW, hb_rewrite as HR, gap_rules as GR
    from harness.tools import t1_compress as T1, t2_schedule as T2, t3_reclose as T3, t4_nameless as T4
    out = ["sweep:" + o for o in SW.OPS if not o.startswith("hr:")]
    out += ["hr:" + o for o in HR.ALL_OPS]
    out += list(T1.OPS) + list(T2.OPS) + list(T3.ALL_OPS) + list(T4.OPS)
    out += ["gr:" + k for k in GR.KINDS]
    out += list(HP_OPS)
    return out


def sweep_op_of(op_id: str) -> str | None:
    """The op name harness/sweep.candidates gives for an op id it generates ("sweep:swap" -> "swap", "hr:clearhyp" -> "hr:clearhyp"),
"""
    if op_id.startswith("sweep:"):
        return op_id[len("sweep:"):]
    if op_id.startswith("hr:") and op_id != "hr:lemmavariant":
        return op_id
    return None
