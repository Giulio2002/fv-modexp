#!/usr/bin/env python3
"""scripts/gen/port-p2w4.py SRC DST [extra a=>b ...] (agent infra, development helper): mechanical first pass of a
window-2 -> window-4 module port (P2W2 -> P2W4) with the frame substitutions. Numeric extras (both sides digits; separator `=>`, or `@@` when the text contains `=>`) are
applied with digit boundaries, simultaneously (no chaining); other extras are plain replacements, applied in order."""
import sys, re
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
# imports of P2W2 modules -> P2W4 modules (except P2W2Defs which P2W4Defs imports)
s = re.sub(r'import FvModexp\.Proofs\.Arm64\.Exp\.P2W2(\w*)', r'import FvModexp.Proofs.Arm64.Exp.P2W4\1', s)
lines = s.split('\n')
last_imp = max(i for i, l in enumerate(lines) if l.startswith('import '))
if 'autoImplicit' not in s:
    lines.insert(last_imp + 1, '\nset_option autoImplicit false')
s = '\n'.join(lines)
s = s.replace('namespace FvModexp.Arm64.P2W2', 'namespace FvModexp.Arm64.P2W4\n\nopen P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)', 1)
s = s.replace('end FvModexp.Arm64.P2W2', 'end FvModexp.Arm64.P2W4')
s = s.replace('FvModexp.Arm64.P2W2.', 'FvModexp.Arm64.P2W4.')
s = s.replace('expNNPowerOfTwoWindowSize2', 'expNNPowerOfTwoWindowSize4')
num = {'560': '848', '456': '744', '472': '760', '464': '752'}
plain = []
for kv in sys.argv[3:]:
    a, b = kv.split('@@', 1) if '@@' in kv else kv.split('=>', 1)
    if re.fullmatch(r'[0-9]+', a) and re.fullmatch(r'[0-9]+', b):
        num[a] = b
    else:
        plain.append((a, b))
# code addresses: [AT 0x1b65f4, body 0x1b6898) shifts by -2148, [LT 0x1b69bc, end 0x1b6ba0) by -2020; the loop
# body [0x1b6898, 0x1b69bc) has a different shape (10 calls) and is reported, not mapped.
SH = [(0x1b65f4, 0x1b6898, -2148), (0x1b69bc, 0x1b6ba0, -2020)]
body = set()
def addr(v):
    for lo, hi, d in SH:
        if lo <= v < hi:
            return v + d
    if 0x1b6898 <= v < 0x1b69bc:
        body.add(hex(v))
    return None
def numf(m):
    t = m.group(0)
    if t in num:
        return num[t]
    a = addr(int(t))
    return str(a) if a is not None else t
s = re.sub(r'(?<![0-9a-zA-Z_.])[0-9]+(?![0-9])', numf, s)
s = re.sub(r'(?<=[a-z])[0-9]{3}(?![0-9])', lambda m: num.get(m.group(0), m.group(0)), s)  # names like r528
def hexf(m):
    a = addr(int(m.group(0), 16))
    return hex(a) if a is not None else m.group(0)
s = re.sub(r'0x1b6[0-9a-f]{3}\b', hexf, s)
if body:
    print('WARNING: loop-body addresses left unmapped:', sorted(body))
for a, b in plain:
    s = s.replace(a, b)
open(dst, 'w').write(s)
