#!/usr/bin/env python3
"""align.py: instruction alignment of expNNOddMontgomeryWindowSize4 -> WindowSize2 (arm64); prints JSON
[[w4_off, w2_off], ...] for every instruction in an equal block (slots >= 816 normalised by -288). Dev tool (expmc)."""
import re, difflib, json, sys
D = '/srv/fv-modexp-ops/cache-expmc/dis/'
def load(f, base):
    out = []
    for l in open(D + f).read().split('\n')[1:]:
        p = [x for x in l.split('\t') if x.strip()]
        if len(p) < 4: continue
        out.append((int(p[1], 16) - base, p[3].strip()))
    return out
w4 = load('nat.expNNOddMontgomeryWindowSize4.arm64.s', 0x1b7170)
w2 = load('nat.expNNOddMontgomeryWindowSize2.arm64.s', 0x1b7eb0)
def norm4(s):
    s = re.sub(r'\b(\d+)\(RSP\)', lambda m: 'S%d(RSP)' % (int(m.group(1)) - 288) if int(m.group(1)) >= 816 else m.group(0), s)
    return re.sub(r'-?\d+\(PC\)', 'PC', s)
def norm2(s):
    s = re.sub(r'\b(\d+)\(RSP\)', lambda m: 'S%d(RSP)' % int(m.group(1)) if int(m.group(1)) >= 528 else m.group(0), s)
    return re.sub(r'-?\d+\(PC\)', 'PC', s)
a = [norm4(x[1]) for x in w4]; b = [norm2(x[1]) for x in w2]
sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
pairs = []
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == 'equal':
        pairs += [[w4[i1 + t][0], w2[j1 + t][0]] for t in range(i2 - i1)]
json.dump(pairs, sys.stdout)
