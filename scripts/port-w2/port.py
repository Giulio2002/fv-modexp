#!/usr/bin/env python3
"""port.py SRC.lean DST.lean: mechanical first pass of a window-4 (arm64) proof module to window-2 (dev tool, expmc).
Rules: W4 -> W2 names, WindowSize4 -> WindowSize2, pc literals of the function mapped through align.json (unmapped:
marked PORT?), the deferwrap closure address, every integer literal in [816, 1040] (frame slots above the powers table,
the frame size 928, the window top 1040) shifted by -288. Window constants (23n, 17n, d < 16, k = 15, LSR 60, iter 4,
...) are NOT touched: review the diff."""
import re, sys, json, os
here = os.path.dirname(os.path.abspath(__file__))
pairs = dict(json.load(open(os.path.join(here, 'align.json'))))
B4, B2, D4, D2 = 0x1b7170, 0x1b7eb0, 1801824, 1805072
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
s = s.replace('WindowSize4', 'WindowSize2').replace('fnW4', 'fnW2').replace('window-4', 'window-2')
s = re.sub(r'\bW4', 'W2', s)
s = re.sub(r'\bExpW4', 'ExpW2', s)
def pc(m):
    v = int(m.group(0))
    if v == D4: return str(D2)
    if B4 <= v < B4 + 0xd00:
        o = v - B4
        return str(B2 + pairs[o]) if o in pairs else m.group(0) + ' /-PORT?-/'
    return m.group(0)
s = re.sub(r'(?<![\w.])\d{7}(?![\w.])', pc, s)
def hexoff(m):
    o = int(m.group(1), 16)
    return m.group(0).replace(m.group(1), hex(pairs[o])) if o in pairs else m.group(0) + ' /-PORT?-/'
s = re.sub(r'segAddr LibExp\.program fn \+ (0x[0-9a-f]+)', hexoff, s)
def slot(m):
    v = int(m.group(2))
    return m.group(1) + (str(v - 288) if 816 <= v <= 1040 else m.group(2))
s = re.sub(r'(^|[^\w.])(\d{3,4})(?![\w.])', slot, s, flags=re.M)
s = re.sub(r'\b([rqh]|rs|sl|rk)(\d{3,4})\b', lambda m: m.group(1) + (str(int(m.group(2)) - 288) if 816 <= int(m.group(2)) <= 1040 else m.group(2)), s)
open(dst, 'w').write(s)
