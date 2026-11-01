#!/usr/bin/env bash
export PATH="$HOME/.elan/bin:$PATH"; cd "$(dirname "$0")"
d=physlib-v4.32.0; echo "[$(date -Is)] cache $d"; ( cd $d && lake exe cache get ) > logs/cache-$d.log 2>&1; echo "[$(date -Is)] cache exit=$? $(tail -1 logs/cache-$d.log)"
echo "[$(date -Is)] build $d"; ( cd $d && lake build Physlib.Mathematics.VariationalCalculus.Basic Physlib.Electromagnetism.Dynamics.IsExtrema Physlib.QFT.PerturbationTheory.WickAlgebra.TimeOrder ) > logs/build-$d.log 2>&1
echo "[$(date -Is)] $d exit=$? $(tail -1 logs/build-$d.log)"; du -sh $d/.lake 2>/dev/null
for v in v4.31.0 v4.30.0 v4.29.0 v4.28.0; do
  d=arklib-$v; echo "[$(date -Is)] cache $d"; ( cd $d && lake exe cache get ) > logs/cache-$d.log 2>&1; echo "[$(date -Is)] cache exit=$? $(tail -1 logs/cache-$d.log)"
  echo "[$(date -Is)] build $d"; ( cd $d && lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude ArkLib.Data.CodingTheory.ProximityGap.DG25.MainResults ) > logs/build-$d.log 2>&1
  echo "[$(date -Is)] $d exit=$? $(tail -1 logs/build-$d.log)"; du -sh $d/.lake 2>/dev/null
done; echo DONE
