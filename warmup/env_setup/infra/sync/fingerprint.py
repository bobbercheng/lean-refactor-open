"""Content fingerprint of run data, to prove a bucket restore holds exactly what the instance has (infra/vast/finalize_a100.sh). Prints
one "sha256  path" line per file under the given repo-relative paths (missing paths are skipped); a verified.jsonl is listed line by line
("sha256  path#line"), because a restore may append outbox records in a different order.
  python3 infra/sync/fingerprint.py harness/work_fresh-a100 probe/runs/fresh-a100-p6 ...     (run from the repo or restore root)
"""
import hashlib, os, sys

for p in sys.argv[1:]:
    files = [p] if os.path.isfile(p) else sorted(os.path.join(d, f) for d, _, fs in os.walk(p) for f in fs) if os.path.isdir(p) else []
    for f in files:
        if os.path.basename(f) == "verified.jsonl":
            for line in sorted({l.strip() for l in open(f, encoding="utf-8", errors="replace") if l.strip()}):
                print(hashlib.sha256(line.encode()).hexdigest(), f + "#line")
        else:
            print(hashlib.sha256(open(f, "rb").read()).hexdigest(), f)
