#!/bin/bash
# genlibexp.sh isa : LibExp (names = top's RunIface.namesExp verbatim) for isa
cd "$(dirname "${BASH_SOURCE[0]}")/.."; isa=$1; I=$([ $isa = arm64 ] && echo Arm64 || echo Amd64)
X=/srv/fv-modexp/build/x-Run-$isa/Extracted.lean
N=$(python3 - /srv/fv-modexp-top/lean/FvModexp/Proofs/Arm64/Top/RunIface.lean <<'PY'
import sys,re
t=open(sys.argv[1]).read(); b=t[t.index('def namesExp'):]; b=b[:b.index(']')]
P="github.com/ethereum/go-bigmodexpfix/src/math/big."
for m in re.finditer(r'(P \+\+ )?"([^"]*)"', b): print((P if m.group(1) else "")+m.group(2))
PY
)
KEEPALL=1 python3 scripts/gen-libprog-sub.py $X $isa LibExp lean/FvModexp/Proofs/$I/Exp/LibExp.lean $N
