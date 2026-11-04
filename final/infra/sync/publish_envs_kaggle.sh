#!/usr/bin/env bash
# Publish the packed Lean toolchains and environments as public Kaggle datasets (pairs with pack_envs.sh; operator 2026-10-09: "use
# Kaggle public dataset for lean env instead of gcp bucket as it's free for Kaggle public dataset", and upload from the A100, not via the
# GB10). Runs ON the instance where the pack is, so the 35 GB crosses the datacenter uplink once. The Kaggle key is account-wide, so it
# never lands on the instance's disk: the GB10 pipes it over SSH into this process's environment (KAGGLE_USERNAME / KAGGLE_KEY) and it is
# gone when the upload ends. Refuses the pack unless its audit passed and every checksum matches, then creates each folder as a public
# dataset (or adds a version when it exists), smallest first. MERGES the pack's rows into infra/vast/envs_kaggle.tsv (dataset, file, bytes,
# sha256), the list infra/sync/restore_envs.sh restores from: rows of files not in this pack are kept (review 2026-10-28: the old
# rewrite dropped the 31 rows of the other datasets). Copy the tsv back to the repo.
# A Kaggle version REPLACES the dataset's file set, so before versioning an existing dataset every file the tsv lists for it that is not
# in the pack folder is downloaded (anonymously, sha256-checked) into the folder first (KEEP_EXISTING=1, the default): the new version
# holds the old files unchanged (same bytes, same sha) plus the new ones. KEEP_EXISTING=0 publishes the folder as it is.
#   python3 -c "import json,os; print(json.load(open(os.path.expanduser('~/.kaggle/kaggle.json')))['key'])" |
#     ssh -p PORT root@HOST 'read -r KAGGLE_KEY; export KAGGLE_KEY KAGGLE_USERNAME=bobber; cd /workspace/lra;
#       setsid nohup infra/sync/publish_envs_kaggle.sh /workspace/envpack > /workspace/envpack/PUBLISH.log 2>&1 < /dev/null &'
# DRY=1: metadata and the merged tsv only, nothing uploaded, no kaggle CLI needed. ENVS_JSON: the environment list the pack was made from.
set -u -o pipefail
cd "$(dirname "$0")/../.." || exit 2
D=${1:-/workspace/envpack}
ENVS_JSON=${ENVS_JSON:-infra/vast/harness_envs.json}; export ENVS_JSON
TSV=${TSV:-infra/vast/envs_kaggle.tsv}; export TSV
OWNER=${KAGGLE_USERNAME:-$(python3 -c "import json, os; print(json.load(open(os.path.expanduser('~/.kaggle/kaggle.json')))['username'])" 2>/dev/null)}
OWNER=${OWNER:-bobber}
log() { echo "[$(date -u -Is)] $*"; }
# the CLI check comes FIRST (review 2026-10-28, finding 5: it was never installed on the instance and the failure came after the checksum pass)
[ "${DRY:-0}" = 1 ] || command -v kaggle > /dev/null || { log "refused: the kaggle CLI is not installed (python3 -m pip install kaggle==2.2.5)"; exit 1; }
[ "${DRY:-0}" = 1 ] || [ -n "${KAGGLE_KEY:-}" ] || [ -f "$HOME/.kaggle/kaggle.json" ] || { log "refused: no Kaggle credential in the environment (KAGGLE_KEY)"; exit 1; }
[ -d "$D" ] && [ -f "$D/PACK.log" ] || { log "refused: no pack at $D"; exit 1; }
tail -n 1 "$D/PACK.log" | grep -q "^PACK DONE" || { log "refused: the pack did not finish clean: $(tail -n 1 "$D/PACK.log")"; exit 1; }
t=$(date +%s); (cd "$D" && sha256sum -c --quiet SHA256SUMS) || { log "refused: an archive changed since it was packed"; exit 1; }
log "checksums ok ($(( $(date +%s) - t ))s)"
# existing files of a dataset about to be versioned: into its folder first, sha256-checked (a Kaggle version replaces the file set)
rm -f "$D/SHA256SUMS.kept"
if [ "${KEEP_EXISTING:-1}" = 1 ] && [ -f "$TSV" ]; then
  while IFS=$'\t' read -r ds f bytes sum; do
    [ -d "$D/$ds" ] || continue
    if [ -f "$D/$ds/$f" ]; then grep -q "	$f	" <<< "$(grep "^$ds	" "$D/MANIFEST.tsv")" && continue; fi   # packed here: the new bytes win
    if [ -f "$D/$ds/$f" ] && echo "$sum  $D/$ds/$f" | sha256sum -c --quiet - 2>/dev/null; then :; else
      log "keeping $ds/$f from the current dataset version ($bytes bytes)"
      ok=0; for a in 1 2 3; do
        curl -sSfL --retry 3 -o "$D/$ds/$f" "${KAGGLE_DL_BASE:-https://www.kaggle.com/api/v1/datasets/download}/$OWNER/$ds/$f" && echo "$sum  $D/$ds/$f" | sha256sum -c --quiet - && { ok=1; break; }
        sleep 5
      done
      [ "$ok" = 1 ] || { log "refused: could not fetch $ds/$f (sha $sum) to keep it in the new version"; rm -f "$D/$ds/$f"; exit 1; }
    fi
    printf '%s  %s/%s\n' "$sum" "$ds" "$f" >> "$D/SHA256SUMS.kept"
  done < <(tail -n +2 "$TSV")
fi
python3 - "$D" "$OWNER" <<'PY'
import csv, json, os, pathlib, sys
D, owner = pathlib.Path(sys.argv[1]), sys.argv[2]
envs = json.load(open(os.environ["ENVS_JSON"]))
rows = list(csv.DictReader(open(D / "MANIFEST.tsv"), delimiter="\t"))
sha = {path: h for h, path in (l.split() for l in (D / "SHA256SUMS").read_text().splitlines())}
tsv = pathlib.Path(os.environ["TSV"])
old = [l.split("\t") for l in tsv.read_text().splitlines()[1:] if l.strip()] if tsv.exists() else []
kept = {tuple(ds_f.split("/", 1)): h for h, ds_f in (l.split() for l in (D / "SHA256SUMS.kept").read_text().splitlines())} if (D / "SHA256SUMS.kept").exists() else {}
names = {"arklib": "ArkLib", "cslib": "cslib", "mathlib": "Mathlib", "physlib": "PhysLib", "strata": "Strata", "leanpool": "LeanPool"}
packed = {(r["dataset"], r["file"]): r for r in rows}
merged = {(ds, f): (ds, f, b, h) for ds, f, b, h in old}            # existing rows, replaced below by this pack's
for (ds, f), r in packed.items():
    merged[(ds, f)] = (ds, f, r["packed_bytes"], sha[ds + "/" + f])
for ds in sorted({r["dataset"] for r in rows}):
    files = [r for r in rows if r["dataset"] == ds]
    extra = [(f, b, h) for (d2, f, b, h) in merged.values() if d2 == ds and (ds, f) not in packed]   # kept from the current version
    for f, b, h in extra:
        if (ds, f) not in kept or kept[(ds, f)] != h:
            if os.environ.get("KEEP_EXISTING", "1") == "1":
                raise SystemExit(f"{ds}/{f} is listed in the tsv but was not fetched into the folder (KEEP_EXISTING)")
    arch = ds.rsplit("-", 2)[-2] + "_" + ds.rsplit("-", 1)[-1]
    allfiles = [f["file"] for f in files] + [f for f, _, _ in extra]
    if ds.startswith("lean4-toolchains"):
        vs = sorted(".".join(f.split("---")[1].split(".")[:2]) for f in allfiles if "---" in f)
        title = f"Lean 4 toolchains {vs[0]}-{vs[-1]} ({arch} Linux)"
        how = "Unpack `elan-home.tar.zst` into `~` and each toolchain into `~/.elan/toolchains/`."
    else:
        g = ds.split("-")[2]; title = f"Prebuilt Lean envs: {names.get(g, g)} ({arch} Linux)"
        how = ("Unpack every archive into one folder `envs/`. Each env is a git worktree of the clone in this dataset (`*.git-main`, or "
               "`mathlib4`) with its `.lake` build; it was built at `/workspace/lra/envs`, so elsewhere run "
               "`git -C envs/<clone> worktree repair envs/<env>` once.")
    assert 6 <= len(title) <= 50, title
    lines = []
    for f in files:
        n = f["file"][:-8]; e = envs.get(n)
        repo = n[:-len(".git-main")] if n.endswith(".git-main") else n
        url = next((v["url"] for v in envs.values() if v["repo"] == repo), "")
        what = (f"`{e['url']}` at `{e['commit']}`" if e else "elan itself and its settings" if n == "elan-home"
                else f"toolchain `leanprover/lean4:{n.split('---')[1]}`" if "---" in n
                else f"git clone of `{url}`" + (" (blobless)" if repo in ("mathlib4", "leanpool") else "") if url else "")
        lines.append(f"| `{f['file']}` | {int(f['packed_bytes']) / 1e9:.2f} GB | {int(f['raw_bytes']) / 1e9:.2f} GB | {what} |")
    for f, b, h in sorted(extra):
        n = f[:-8]
        what = ("elan itself and its settings" if n == "elan-home" else f"toolchain `leanprover/lean4:{n.split('---')[1]}`" if "---" in n
                else "unchanged from the previous version")
        lines.append(f"| `{f}` | {int(b) / 1e9:.2f} GB | | {what} |")
    desc = (f"{title}, packed as `tar | zstd`: `zstd -dc FILE | tar -xf - -C DIR`.\n\n{how}\n\n"
            "| file | packed | unpacked | contents |\n|---|---|---|---|\n" + "\n".join(lines) +
            "\n\nEvery component keeps its upstream license; see the LICENSE file inside each archive.")
    (D / ds / "dataset-metadata.json").write_text(json.dumps(
        {"title": title, "id": f"{owner}/{ds}", "licenses": [{"name": "other"}], "description": desc}, indent=1))
order = {(ds, f): i for i, (ds, f, _, _) in enumerate(old)}
out = ["dataset\tfile\tbytes\tsha256"] + ["\t".join(v) for k, v in sorted(merged.items(), key=lambda kv: (kv[0][0], order.get(kv[0], 10 ** 6), kv[0][1]))]
if tsv.exists():
    tsv.with_suffix(".tsv.bak").write_text(tsv.read_text())
tsv.write_text("\n".join(out) + "\n")
print(f"{tsv}: {len(old)} rows before, {len(merged)} after ({len(packed)} from this pack)")
PY
[ $? = 0 ] || { log "refused: metadata step failed"; exit 1; }
[ "${DRY:-0}" = 1 ] && { log "dry run: metadata and $TSV written (merged), nothing uploaded"; exit 0; }
BAD=0
for ds in $(du -sb "$D"/*/ | sort -n | awk '{print $2}'); do
  s=$(basename "$ds"); [ "$s" = index ] && continue; t=$(date +%s)
  if kaggle datasets status "$OWNER/$s" > /dev/null 2>&1; then
    kaggle datasets version -p "$ds" -m "repack $(date -u +%F)" -q > "$D/upload-$s.log" 2>&1 && log "versioned $OWNER/$s ($(( $(date +%s) - t ))s)" || { log "version $s FAILED: $(tail -n 2 "$D/upload-$s.log")"; BAD=1; }
  else
    kaggle datasets create -p "$ds" --public -q > "$D/upload-$s.log" 2>&1 && log "created $OWNER/$s ($(( $(date +%s) - t ))s)" || { log "create $s FAILED: $(tail -n 2 "$D/upload-$s.log")"; BAD=1; }
  fi
done
[ "$BAD" = 0 ] && log "PUBLISH DONE" || log "PUBLISH FAILED"
