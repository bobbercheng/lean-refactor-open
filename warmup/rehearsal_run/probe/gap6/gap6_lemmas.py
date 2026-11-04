#!/usr/bin/env python3
"""gap6 harness-run lemma search for the 'mirror' step (generic, $0): for each row, the files its context.lean imports (in the row's own
env checkout, first pinned version), every theorem/lemma whose name contains symm / comm / swap / _iff. GLM gets the names, not advice.
    python3 gap6_lemmas.py ROWS.jsonl WORK_ROOT ENVS_DIR OUT.json [name ...]"""
import json, re, sys
from pathlib import Path

PAT = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma)\s+([A-Za-z0-9_.'?!]*(?:symm|comm|swap|_iff)[A-Za-z0-9_.'?!]*)", re.M)


def search(row: dict, work: Path, envs: Path) -> list:
    ctx = work / "context.lean"
    if not ctx.exists():
        return []
    ver = next(iter(row["version_info"][0]))
    env = envs / f"{row['source']}-{ver}"
    out = []
    for m in re.findall(r"^(?:public\s+)?import\s+(\S+)", ctx.read_text(), re.M):
        f = env / (m.replace(".", "/") + ".lean")
        if f.exists():
            out += [x for x in PAT.findall(f.read_text()) if x not in out]
    return out


if __name__ == "__main__":
    rows = {json.loads(l)["name"]: json.loads(l) for l in open(sys.argv[1]) if l.strip()}
    work, envs, outp = Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4])
    want = sys.argv[5:] or list(rows)
    res = json.loads(outp.read_text()) if outp.exists() else {}
    for n in want:
        d = work / re.sub(r"[^A-Za-z0-9_.-]", "_", n)
        res[n] = search(rows[n], d, envs)
        print(n.split(".")[-1][:40], len(res[n]), res[n][:8])
    outp.write_text(json.dumps(res, indent=1, ensure_ascii=False))
