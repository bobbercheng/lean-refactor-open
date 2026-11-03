#!/usr/bin/env bash
# After a pre-emption + re-rent (2026-10-08): provision a new instance, then restart the A100 work on its id: LR-eval chain (resumes from the saved
# samples), worker-scaling test, second-model trial; each with its hold file so nothing releases the instance early.
#   --inplace: no new rental; wait until the pre-empted instance runs again and its server is UP (checked every 2 min, real path incl. bridge),
#              then restart the same three jobs on it (2026-10-08 06:21 pre-emption: the chain gave up and KEPT the instance).
#   JOBS="lra-trial" (env): restart only these jobs and create only their holds (11:04 pre-emption during the trial: the eval and the
#              scale test were already done and must not run again).
set -u
cd "${REPO_ROOT:-$(dirname "$0")/../..}" || exit 2
. infra/vast/common.sh; require vastai python3
log() { echo "[$(date -u -Is)] $*"; }
if [ "${1:-}" = --inplace ]; then
  ID=$(cat probe/a100-instance-id); log "waiting for instance $ID to resume in place"
  until vastai show instance "$ID" --raw 2>/dev/null | python3 -c 'import json,sys; sys.exit(0 if json.load(sys.stdin).get("actual_status")=="running" else 1)' \
        && { systemctl --user restart lra-bridge 2>/dev/null; sleep 20; infra/vast/server_up.sh "$ID" --bridge > /dev/null 2>&1; }; do sleep 120; done
  log "instance $ID running and server UP; restarting the A100 work"
else
  CONFIRM=yes infra/vast/provision.sh 2 || { log "provision failed; nothing restarted"; exit 1; }
  ID=$(cat probe/a100-instance-id); log "new instance $ID ready; restarting the A100 work"
fi
echo glm-5.3-flash > probe/a100-served-model
JOBS=${JOBS:-lra-lreval lra-scale lra-trial}
has() { case " $JOBS " in *" $1 "*) return 0;; esac; return 1; }
has lra-scale && echo "scale test (infra/vast/scale_test.sh), set $(date -u +%FT%H:%M)" > probe/a100-hold-$ID
has lra-trial && echo "model trial (Leanstral 1.5, Qwen3.8-27B, Goedel-Prover-V2-32B), set $(date -u +%FT%H:%M)" > probe/a100-hold-trial-$ID
has lra-lreval && rm -f probe/lr_eval/A100_EVAL_DONE probe/lr_eval/A100_EVAL_KEPT
for U in $JOBS; do systemctl --user stop $U 2>/dev/null; done
has lra-lreval && systemd-run --user --unit=lra-lreval --collect -p WorkingDirectory="$PWD" -E PATH="$PATH" -E REPO_ROOT="$PWD" /usr/bin/bash -c "exec infra/vast/lreval_chain.sh $ID >> probe/lr_eval/a100-chain.log 2>&1" >/dev/null
has lra-scale && systemd-run --user --unit=lra-scale --collect -p WorkingDirectory="$PWD" -E PATH="$PATH" -E HOME="$HOME" -E REPO_ROOT="$PWD" -E LRA_LEAN_MEMORY_MB=16000 /usr/bin/bash -c "exec infra/vast/scale_test.sh $ID >> probe/a100-scale-test.log 2>&1" >/dev/null
has lra-trial && systemd-run --user --unit=lra-trial --collect -p WorkingDirectory="$PWD" -E PATH="$PATH" -E HOME="$HOME" -E REPO_ROOT="$PWD" /usr/bin/bash -c "exec infra/vast/model_trial.sh $ID >> probe/a100-model-trial.log 2>&1" >/dev/null
log "restarted $JOBS on $ID"
