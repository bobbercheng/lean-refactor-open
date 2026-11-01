"""Import verified.jsonl records from probe runs into the bank (idempotent)."""
import json, sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from bank.store import write_record
n=0
for f in pathlib.Path("probe/runs").glob("*/verified.jsonl"):
    if f.parent.name.startswith("exp-"):
        continue  # experiments (e.g. a z.ai test on a copy of the A100 line's state) never enter the bank (2026-10-09)
    for l in f.open():
        if l.strip():
            rec=json.loads(l)
            if (rec.get("provenance") or {}).get("kind") == "closed-dev-only":
                continue  # closed models (Claude via Claude Code) are comparison-only; never in the bank
            write_record(rec); n+=1
print("imported", n, "records")
