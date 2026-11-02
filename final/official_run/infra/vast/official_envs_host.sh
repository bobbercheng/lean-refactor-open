#!/usr/bin/env bash
# ON the A100 host, from the export root (/workspace/lra): the Lean environments of the OFFICIAL rows (docs/open_official_run_runbook.md
# section 3). It never deletes anything: when the disk is short it lists the env directories no official row and no live run needs
# (prune candidates, with sizes) and stops; deleting them is the operator's call (runbook 3.3).
#   bash infra/vast/official_envs_host.sh ROWS ENVS_JSON check   check_envs.py on ROWS: "ENVS OK" (exit 0) or the missing list (exit 1)
#   bash infra/vast/official_envs_host.sh ROWS ENVS_JSON plan    the env entries of ENVS_JSON (envs_from_rows.py) still missing (no env dir, no
#                                                               lean-toolchain, or a row module's .olean not built) -> infra/vast/harness_envs.
#                                                               missing.json; the disk they need (~9 GB per Mathlib-cached env, 1 GB otherwise,
#                                                               0.5 GB for modules in an existing env) against the free space - MARGIN_GB (20);
#                                                               prune candidates. Last line "PLAN ok ..." (exit 0) or "PLAN NEED-PRUNE ..." (exit 3)
#   bash infra/vast/official_envs_host.sh ROWS ENVS_JSON build   plan; when it is ok, the missing envs built by infra/vast/harness_setup.sh with
#                                                               ENVS_JSON = the missing list, DETACHED (nice 5; log envs/logs/official_setup.log,
#                                                               last line "SETUP DONE ok=N failed=M"); the old setup-repo logs are moved to
#                                                               envs/logs/old-<ts>/ first (their "ENV OK <env>" lines would skip a new module of
#                                                               an env that already exists). Poll: `check`.
# KEEP_ROWS: rows files of runs that are alive or may resume (default /workspace/lra-run-p85b/rows.jsonl when it exists): their envs are
# never prune candidates.
set -u
cd "$(dirname "$0")/../.." || exit 2
ROWS=${1:?rows}; EJ=${2:?envs json}; MODE=${3:-check}; MARGIN_GB=${MARGIN_GB:-20}; DF_PATH=${DF_PATH:-/workspace}
KEEP_ROWS=${KEEP_ROWS-$( [ -f /workspace/lra-run-p85b/rows.jsonl ] && echo /workspace/lra-run-p85b/rows.jsonl)}
mkdir -p envs/logs
log() { echo "[$(date -u -Is)] official-envs: $*"; }
if [ "$MODE" = check ]; then
  python3 infra/open_package/check_envs.py --rows "$ROWS" --root "$PWD" > envs/logs/official_check.txt 2>&1; rc=$?
  tail -n 1 envs/logs/official_check.txt; [ "$rc" = 0 ] && { echo "ENVS OK"; exit 0; }
  grep "^MISSING" envs/logs/official_check.txt | head -n 30; exit 1
fi
FREE=$(df --output=avail -BG "$DF_PATH" 2>/dev/null | tail -n 1 | tr -dc 0-9)
python3 - "$ROWS" "$EJ" "${FREE:-0}" "$MARGIN_GB" "$KEEP_ROWS" > envs/logs/official_plan.txt <<'PY'
import json, subprocess, sys
from pathlib import Path
rows_p, ej_p, free, margin, keep_rows = sys.argv[1], sys.argv[2], float(sys.argv[3] or 0), float(sys.argv[4]), sys.argv[5].split()
PROJECT_DIRS = {"strata": "strata", "cslib": "cslib", "physlib": "physlib", "arklib": "arklib", "leanpool": "leanpool", "putnambench": "mathlib"}
envs = json.load(open(ej_p)); rows = [json.loads(l) for l in open(rows_p) if l.strip()]
unknown = sorted({r["source"] for r in rows} - set(PROJECT_DIRS))
if unknown:
    print(f"UNKNOWN-SOURCE {' '.join(unknown)}: check_envs.py / envs_from_rows.py need the new project (runbook 3.2)")
need_mods = {}   # env key -> module oleans the official rows need
for r in rows:
    d = PROJECT_DIRS.get(r["source"], r["source"])
    for vi in r["version_info"]:
        for ver in vi:
            need_mods.setdefault(f"{d}-{ver}", set())
            if r["source"] != "putnambench":
                need_mods[f"{d}-{ver}"].add(str(Path(r["file_path"]).with_suffix(".olean")))
missing, need_gb = {}, 0.0
for k, v in envs.items():
    e = Path("envs") / k
    gone = [m for m in sorted(need_mods.get(k, ())) if not (e / ".lake/build/lib/lean" / m).exists()]
    incomplete = k.startswith("mathlib-") and e.is_dir() and not (e / ".lake/build/lib/lean/Mathlib.olean").exists()
    if not e.is_dir() or not (e / "lean-toolchain").exists() or gone or incomplete:
        missing[k] = v
        need_gb += (0.5 if e.is_dir() else (9.0 if v.get("cache") else 1.0))
        print(f"MISSING {k}: {'env dir absent' if not e.is_dir() else ('modules not built: ' + ', '.join(gone[:3]) if gone else 'incomplete')}")
json.dump(missing, open("infra/vast/harness_envs.missing.json", "w"), indent=1)
keep = set(need_mods)
for kr in keep_rows:
    try:
        for l in open(kr):
            if l.strip():
                r = json.loads(l); d = PROJECT_DIRS.get(r["source"], r["source"])
                keep |= {f"{d}-{ver}" for vi in r["version_info"] for ver in vi}
    except OSError:
        pass
cands = []
for e in sorted(Path("envs").iterdir()):
    if not e.is_dir() or e.name in keep or e.name.endswith(".git-main") or e.name in ("mathlib4", "logs") or "-v" not in e.name:
        continue
    out = subprocess.run(["du", "-s", "--block-size=1G", str(e)], capture_output=True, text=True).stdout.split()
    gb = int(out[0]) if out else 0
    cands.append((e.name, gb)); print(f"PRUNE-CANDIDATE envs/{e.name} {gb} GB (no official row and no KEEP_ROWS row uses it)")
json.dump(cands, open("envs/logs/official_prune.json", "w"))
ok = free >= need_gb + margin and not unknown
print(f"PLAN {'ok' if ok else ('UNKNOWN-SOURCE' if unknown else 'NEED-PRUNE')} missing={len(missing)} need_gb={need_gb:.0f} free_gb={free:.0f} "
      f"margin_gb={margin:.0f} prunable_gb={sum(g for _, g in cands)}")
sys.exit(0 if ok else 3)
PY
rc=$?; cat envs/logs/official_plan.txt
[ "$MODE" = plan ] && exit "$rc"
[ "$rc" = 0 ] || { log "NOT building (plan above): free the listed prune candidates (operator decision, runbook 3.3) or add the new project, then re-run build"; exit 3; }
[ "$(python3 -c "import json; print(len(json.load(open('infra/vast/harness_envs.missing.json'))))")" = 0 ] && { log "nothing missing in the env list; check: $(python3 infra/open_package/check_envs.py --rows "$ROWS" --root "$PWD" | tail -n 1)"; exit 0; }
pgrep -f "[h]arness_setup.sh" > /dev/null && { log "a harness_setup.sh is already running: poll envs/logs/official_setup.log"; exit 0; }
OLD=envs/logs/old-$(date +%s); mkdir -p "$OLD"; mv envs/logs/setup-repo-*.log "$OLD/" 2>/dev/null
ENVS_JSON=infra/vast/harness_envs.missing.json setsid nohup nice -n 5 bash infra/vast/harness_setup.sh > envs/logs/official_setup.log 2>&1 < /dev/null &
log "building $(python3 -c "import json; print(' '.join(json.load(open('infra/vast/harness_envs.missing.json'))))") detached (pid $!; log envs/logs/official_setup.log; ends with SETUP DONE ok=N failed=M)"
