#!/usr/bin/env python3
"""scripts/gen/port-p2w4.py SRC DST (agent infra, development helper): mechanical first pass of [extra a=b ...]: window-2 -> window-4 module port (P2W2 -> P2W4) with the frame substitutions."""
import sys, re
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
# imports of P2W2 modules -> P2W4 modules (except P2W2Defs which P2W4Defs imports)
s = re.sub(r'import FvModexp\.Proofs\.Arm64\.Exp\.P2W2(\w+)', r'import FvModexp.Proofs.Arm64.Exp.P2W4\1', s)
lines = s.split('\n')
last_imp = max(i for i, l in enumerate(lines) if l.startswith('import '))
if 'autoImplicit' not in s:
    lines.insert(last_imp + 1, '\nset_option autoImplicit false')
s = '\n'.join(lines)
s = s.replace('namespace FvModexp.Arm64.P2W2', 'namespace FvModexp.Arm64.P2W4\n\nopen P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)', 1)
s = s.replace('end FvModexp.Arm64.P2W2', 'end FvModexp.Arm64.P2W4')
s = s.replace('expNNPowerOfTwoWindowSize2', 'expNNPowerOfTwoWindowSize4')
for a, b in [('560', '848'), ('456', '744'), ('472', '760'), ('464', '752')]:
    s = re.sub(r'(?<![0-9])' + a + r'(?![0-9])', b, s)
for kv in sys.argv[3:]:
    a, b = kv.split('=>', 1)
    s = s.replace(a, b)
open(dst, 'w').write(s)
