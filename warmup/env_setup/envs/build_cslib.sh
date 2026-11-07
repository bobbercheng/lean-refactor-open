#!/usr/bin/env bash
export PATH="$HOME/.elan/bin:$PATH"; cd "$(dirname "$0")"
for v in v4.33.0-rc2 v4.32.0 v4.31.0 v4.30.0; do
  d=cslib-$v; echo "[$(date -Is)] cache $d"
  ( cd $d && lake exe cache get ) > logs/cache-$d.log 2>&1; echo "[$(date -Is)] cache exit=$? $(tail -1 logs/cache-$d.log)"
  echo "[$(date -Is)] build $d"
  ( cd $d && lake build Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Safety Cslib.Languages.CombinatoryLogic.Confluence Cslib.Languages.CCS.BehaviouralTheory ) > logs/build-$d.log 2>&1
  echo "[$(date -Is)] $d exit=$? $(tail -1 logs/build-$d.log)"; du -sh $d/.lake 2>/dev/null
done; echo DONE
