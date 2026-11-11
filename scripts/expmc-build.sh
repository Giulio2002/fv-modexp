#!/usr/bin/env bash
# expmc-build.sh ISA: clean dev build of the agent-expmc modules (montgomery layer) for ISA into a fresh olean dir;
# prints wall/RSS per module. Development only (the real gate is the lake build / janus verify of the rows).
set -e
isa=$1; I=$([ $isa = arm64 ] && echo Arm64 || echo Amd64)
export OUT=/srv/fv-modexp-ops/cache-expmc/dev/clean-$isa
rm -rf $OUT; mkdir -p $OUT
d=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
$d/dev-lean-expmc.sh -x $isa /srv/fv-modexp/build/x-Run-$isa/Extracted.lean
for m in Common/ExpBase Common/ExpMont Common/MaskWord Common/ExpmcWin Common/ExpmcFrame \
         $I/Exp/LibMont $I/Exp/MontHyp $I/Exp/MontExit $I/Exp/MontLoop $I/Exp/Mont; do
  $d/dev-lean-expmc.sh -x $isa $d/../lean/FvModexp/Proofs/$m.lean 2>&1 | grep -E "^==|KB|error|sorry"
done
