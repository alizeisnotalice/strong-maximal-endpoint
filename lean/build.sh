#!/usr/bin/env bash
# Compile every module in dependency order and run the axiom audit.
# Requires `elan`; the toolchain is pinned by ./lean-toolchain and Mathlib by
# ./lakefile.lean + ./lake-manifest.json.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
OUT=.lake/build/lib/lean
mkdir -p "$OUT/StrongMaximal"
MODULES=(StrongMaximal.Constants StrongMaximal.ExpModel StrongMaximal.Gaussian StrongMaximal.Basic
         StrongMaximal.Cumulants StrongMaximal.StepModel StrongMaximal.NStepModel StrongMaximal.Variance StrongMaximal.ExpMoment StrongMaximal.Mills StrongMaximal.Zeta
         StrongMaximal.Main StrongMaximal.SecondOrder StrongMaximal.Endpoint
         StrongMaximal.Transfer StrongMaximal.TestInput
         StrongMaximal.Plateau StrongMaximal.HwModel StrongMaximal.Threshold
         StrongMaximal.RankRat StrongMaximal StrongMaximal.Audit)
for m in "${MODULES[@]}"; do
  src="${m//.//}.lean"
  echo "== compiling $src"
  lake env lean -o "$OUT/${m//.//}.olean" "$src"
done
echo "== audit (see stdout above)"
