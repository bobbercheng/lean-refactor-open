#!/usr/bin/env bash
export PATH="$HOME/.elan/bin:$PATH"; cd "$(dirname "$0")"
for v in v4.26.0 v4.27.0 v4.29.1; do
  d=strata-$v; echo "[$(date -Is)] build $d"
  ( cd $d && lake build Strata.Transform.CallElimCorrect Strata.Languages.Core.StatementSemanticsProps ) > logs/build-$d.log 2>&1
  echo "[$(date -Is)] $d exit=$? $(tail -1 logs/build-$d.log)"; du -sh $d/.lake 2>/dev/null
done; echo DONE
