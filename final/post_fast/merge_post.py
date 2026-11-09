#!/usr/bin/env python3
"""merge_post.py EMITTED ROWS PROOFS (POST-HOC 2026-11-06): each row of PROOFS is replaced by its line in EMITTED when that line's
stored score is at least the row's current one and its proof passes the export's own static check, so a row never goes down, whatever a read
in mid-run offers. The names must equal the rows file's, in order. Every write is a rename: on any error or kill PROOFS stays whole."""
import json, os, statistics, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scorer.forbidden import check_forbidden


def lines(p):
    return [json.loads(l) for l in Path(p).read_text().splitlines() if l.strip()]


def stored(r):
    s = r.get("stored_score")
    return float(s) if isinstance(s, (int, float)) and not isinstance(s, bool) else float("-inf")


def good(new, cur, row):
    proof = (new.get("proof") or "").rstrip()
    return stored(new) >= stored(cur) and row["statement"].strip() in proof and check_forbidden(proof) is None


def write(path, text):
    tmp = path.with_name(f"{path.name}.{os.getpid()}.post.tmp")
    tmp.write_text(text)
    fd = os.open(tmp, os.O_RDONLY); os.fsync(fd); os.close(fd)
    os.replace(tmp, path)


def main(emitted, rows, proofs):
    cur, new, rs = lines(proofs), lines(emitted), lines(rows)
    names = [r["name"] for r in rs]
    if [r["name"] for r in cur] != names or [r["name"] for r in new] != names:
        sys.exit("merge refused: the names differ from the rows file; proofs.jsonl stays as it is")
    keep = [n if good(n, c, r) else c for c, n, r in zip(cur, new, rs)]
    text = "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in keep)
    write(Path(proofs).with_name("proofs.merged.jsonl"), text)   # read back after a re-run or `run.sh export`, which write the picks
    write(Path(proofs), text)
    print(f"merge: {sum(a['proof'] != b['proof'] for a, b in zip(cur, keep))} of {len(keep)} rows changed, stored mean "
          f"{statistics.mean(stored(r) for r in cur):.4f} -> {statistics.mean(stored(r) for r in keep):.4f}")


if __name__ == "__main__":
    main(*sys.argv[1:4])
