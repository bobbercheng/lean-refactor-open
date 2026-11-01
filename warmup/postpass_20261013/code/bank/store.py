"""Per-problem bank of verified proof variants (PLAN.md §7.2). One JSON file
per record at bank/<problem>/<sha256>.json. The bank only grows."""
from __future__ import annotations

import hashlib, json, re, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BANK = ROOT / "bank"
DEV_ONLY_KINDS = {"api-dev-only"}


def normalize(proof: str) -> str:
    return re.sub(r"[ \t]+\n", "\n", proof.strip()) + "\n"


def sha(proof: str) -> str:
    return hashlib.sha256(normalize(proof).encode()).hexdigest()


def write_record(rec: dict) -> Path:
    rec = dict(rec)
    rec["sha256"] = sha(rec["proof"])
    rec.setdefault("created_at", time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    d = BANK / rec["problem"]
    d.mkdir(parents=True, exist_ok=True)
    p = d / f"{rec['sha256']}.json"
    if not p.exists():
        p.write_text(json.dumps(rec, ensure_ascii=False, indent=1))
    return p


def load_all(problem: str | None = None) -> list[dict]:
    out = []
    for d in sorted(BANK.iterdir()):
        if not d.is_dir() or (problem and d.name != problem):
            continue
        for f in d.glob("*.json"):
            out.append(json.loads(f.read_text()))
    return out


def eligible(rec: dict) -> bool:
    """Submission-eligible: compiled on the primary toolchain and not produced
    by an API-hosted model (compliance rule §10.8)."""
    return bool(rec.get("primary_ok")) and rec.get("provenance", {}).get("kind") not in DEV_ONLY_KINDS
