#!/usr/bin/env bash
# asm-perf.sh: compile every asm proof module (library programs, Common/Asm*, Arm64|Amd64 *Sum, AsmModels) from scratch in
# dependency order with scripts/dev-lean.sh and print `module seconds peakKB` (docs/PERF.md, asm section).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root/lean"
OUT=${OUT:-/srv/fv-modexp-ops/cache-asm/dev/perf}; rm -rf "$OUT"; mkdir -p "$OUT"
mods=$(python3 - <<'PY'
import re,os,glob
fs=[f for f in glob.glob('FvModexp/Proofs/**/*.lean',recursive=True)]
want=set()
for f in fs:
    b=os.path.basename(f)
    if f.startswith('FvModexp/Proofs/Lib/') or (f.startswith('FvModexp/Proofs/Common/') and (b.startswith('Asm') or b.startswith('Fvu'))) \
       or b.endswith('Sum.lean') or b=='AsmModels.lean':
        want.add(f[:-5].replace('/','.'))
deps={}
def imports(m):
    p=m.replace('.','/')+'.lean'
    return [l.split()[1] for l in open(p) if l.startswith('import ') and l.split()[1].startswith('FvModexp.')]
order=[];seen=set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imports(m): visit(d)
    order.append(m)
for m in sorted(want): visit(m)
print(' '.join(m.replace('.','/')+'.lean' for m in order))
PY
)
for f in $mods; do
  r=$(OUT=$OUT "$root/scripts/dev-lean.sh" "$f" 2>&1 | grep -oE '\[[0-9.]+ s, [0-9]+ KB\]' | tail -1)
  echo "$f $r"
done
