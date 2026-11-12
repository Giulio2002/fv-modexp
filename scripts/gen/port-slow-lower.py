#!/usr/bin/env python3
"""port-slow-lower.py: generate the LOWER-loop modules of nat.expNNSlow (arm64) from the upper-loop ones (agent expmc).
SlowK -> SlowK2, SlowU1/U2/U3 -> SlowL1/L2/L3: slot numbers, pcs, return indices, names, and the loop-counter
semantics (`w` = the word index `i` (slot 216, R8), `j < 64`). Usage: port-slow-lower.py LEANDIR"""
import re, sys, os
d = os.path.join(sys.argv[1], 'FvModexp/Proofs/Arm64/Exp')
slots = {336: 384, 120: 248, 128: 240, 208: 200, 352: 392, 168: 264, 176: 256, 360: 400, 184: 280, 192: 272,
         416: 376, 312: 224, 304: 232, 408: 368, 296: 328, 288: 320, 152: 216}
plain = [('fnE + 0x208', 'fnE + 0x3d8'), ('fnE + 0x254', 'fnE + 0x424'), ('fnE + 0x2a4', 'fnE + 0x474'),
         ('fnE + 0x2b4', 'fnE + 0x484'), ('fnE + 0x31c', 'fnE + 0x4ec'), ('4 * 149', '4 * 265'), ('4 * 169', '4 * 285'),
         ('4 * 199', '4 * 315'), ('(idx := 149)', '(idx := 265)'), ('(idx := 169)', '(idx := 285)'),
         ('(idx := 199)', '(idx := 315)'), ('until [1788872]', 'until [1789336]'), ('until [1789044]', 'until [1789508]'),
         ('KT1', 'KT2'), ('KS1', 'KS2'), ('KD1', 'KD2'), ('callU', 'callL'), ('segU', 'segL'), ('wsU', 'wsL'),
         ('Exp.SlowK\n', 'Exp.SlowK2\n'),
         # loop-counter semantics
         ('jw : j ≤ w', 'jw : j ≤ 64'), ('jw : j < w', 'jw : j < 64'), ('w63 : w ≤ 63', 'w63 : w + 2 ≤ yl'),
         ('(hjw : j < w)', '(hjw : j < 64)'), ('(hjw : j ≤ w)', '(hjw : j ≤ 64)'), ('(hw63 : w ≤ 63)', '(hw63 : w + 2 ≤ yl)'),
         ('  e14 : S.regs 14 = BitVec.ofNat 64 w\n', ''), ('e8 : S.regs 8 = BitVec.ofNat 64 yl', 'e8 : S.regs 8 = BitVec.ofNat 64 w'),
         ('have e14 := hk.e14; ', ''), ('\n    (e14 : T.regs 14 = BitVec.ofNat 64 w) (e3 :', '\n    (e3 :'),
         ('(e8 : T.regs 8 = BitVec.ofNat 64 yl)', '(e8 : T.regs 8 = BitVec.ofNat 64 w)'), ('e9, e14, e3', 'e9, e3')]
def port(src, dst, extra=()):
    s = open(os.path.join(d, src)).read()
    s = s.replace('sp + 120 ≤ a', 'SPLO_A')
    for a, b in list(extra) + plain:
        s = s.replace(a, b)
    s = re.sub(r'(sp \+ |\bs|\br|\bq)(\d+)\b', lambda m: m.group(1) + str(slots.get(int(m.group(2)), int(m.group(2)))), s)
    s = s.replace('upper', 'lower').replace('Upper', 'Lower').replace('Exp.SlowK_', 'Exp.SlowK').replace('SPLO_A', 'sp + 120 ≤ a')
    open(os.path.join(d, dst), 'w').write(s)
port('SlowK.lean', 'SlowK2.lean', [('theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by\n'
     '  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega\n\n', ''),
     ('import FvModexp.Proofs.Arm64.Exp.SlowJF', 'import FvModexp.Proofs.Arm64.Exp.SlowK_')])
port('SlowU1.lean', 'SlowL1.lean')
port('SlowU2.lean', 'SlowL2.lean', [('a + 8 ≤ sp + 304 ∨ sp + 320 ≤ a ∧ a + 8 ≤ sp + 416',
     'a + 8 ≤ sp + 224 ∨ sp + 240 ≤ a ∧ a + 8 ≤ sp + 376 ∨ sp + 384 ≤ a')])
port('SlowU3.lean', 'SlowL3.lean', [('a + 8 ≤ sp + 288 ∨ sp + 304 ≤ a ∧ a + 8 ≤ sp + 408 ∨ sp + 416 ≤ a',
     'a + 8 ≤ sp + 320 ∨ sp + 336 ≤ a ∧ a + 8 ≤ sp + 368 ∨ sp + 376 ≤ a'),
     ('?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hbud', '?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hbud')])
