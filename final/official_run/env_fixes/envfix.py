"""Env-side workaround for the 5 rows whose reference fails in our measured compile (2026-11-01).
For each row and EACH of its pins: in the env's copy of the row's file, strip the trailing ` in` from the chain of
`open|omit|set_option|include|unseal|variable ... in` lines directly above the declaration (docstrings/attributes/blank lines skipped).
Line count is unchanged; the compile path truncates the file after the declaration, so the now-global commands reach only the theorem
(and the arena_measure elab, which they already reached). Dry run by default; --apply writes, backups to BACKUP.
usage: python3 envfix.py ROOT ROWS [--apply] [--backup DIR]"""
import sys, json, re, shutil
from pathlib import Path
root, rows_path = Path(sys.argv[1]), sys.argv[2]
apply = "--apply" in sys.argv
backup = Path(sys.argv[sys.argv.index("--backup") + 1]) if "--backup" in sys.argv else Path("/workspace/final-in/envfix_backup")
sys.path.insert(0, str(root))
from scorer import compile as C
NAMES = {"HermitianMat.inv_convex", "Lambda.callOfLFunc_eraseMetadata_congr",
         "ProximityGap.RS_exists_nonzero_kernelVec_of_det_eq_zero_natDegree_le_one",
         "ProximityGap.RS_jointAgreement_of_goodCoeffs_card_gt", "Vlasov.transportedIntegral_continuousOn"}
for r in map(json.loads, open(rows_path)):
    if r["name"] not in NAMES: continue
    for d in r["version_info"]:
        pin = next(iter(d)); f = C.project_env_dir(r["source"], pin) / r["file_path"]
        if not f.exists(): print(f"SKIP {r['name']} {pin}: no {f}"); continue
        prefix = C.file_prefix(r, pin); lines = prefix.split("\n"); i = len(lines) - 2; changed = []
        while i >= 0:
            s = lines[i].strip()
            if s.endswith("-/"):
                while i >= 0 and not lines[i].lstrip().startswith("/-"): i -= 1
                i -= 1; continue
            if re.match(r"(open|omit|set_option|include|unseal|variable)\b.*\bin$", s):
                new = re.sub(r"\s+in\s*$", "", lines[i]); changed.append((i + 1, lines[i], new)); lines[i] = new; i -= 1; continue
            if s.startswith("@[") or s == "": i -= 1; continue
            break
        if not changed: print(f"OK   {r['name']} {pin}: no `... in` chain above the declaration (nothing to do)"); continue
        for ln, old, new in sorted(changed): print(f"EDIT {r['name']} {pin} {f.relative_to(root)}:{ln}: {old.strip()!r} -> {new.strip()!r}")
        if apply:
            b = backup / f"{f.parent.parent.name}__{pin}__{f.name}" if False else backup / (str(f.relative_to(root)).replace("/", "__"))
            b.parent.mkdir(parents=True, exist_ok=True)
            if not b.exists(): shutil.copy2(f, b)
            text = f.read_text(); assert text.startswith(prefix)
            f.write_text("\n".join(lines) + text[len(prefix):])
