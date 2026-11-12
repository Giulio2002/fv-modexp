#!/usr/bin/env python3
"""gen-run-dj2-64.py -- (agent top) generate lean/FvModexp/Proofs/Amd64/Top/RunDJ{S,F,Z}2.lean (modulus operand: the
join J2 -> memmove/skip -> setBytes call pcE2) from the exponent-operand files RunDJ{S,F,Z}1.lean by substitution.
Differences: the copy length is in DX (not R11), the dst spill is e-264, no slot is stored after the copy (e-552 is
already set at D2), operands 0 and 1 are done."""
import os, re, sys
d = os.path.dirname(os.path.abspath(__file__)) + "/../lean/FvModexp/Proofs/Amd64/Top"
H0, H1, H2 = "hdrV s p len 0", "hdrV s p len 1", "hdrV s p len 2"
def conv(kind):
    t = open(f"{d}/RunDJ{kind}1.lean").read()
    R = [
        (H1, "@H2@"), (H0, "@A@"),
        (f"theorem dJ{kind}1", f"theorem dJ{kind}2"),
        ("operand 1", "operand 2"), ("`J1` (`fn + 0x840`)", "`J2` (`fn + 0x9c7`)"), ("`n = R11`", "`n = DX`"),
        ("`fn + 0x855`", "`fn + 0x9dc`"), ("`e - 552 = h0 + h1` is stored and t", "t"), ("h1, h1)", "h2, h2)"),
        ("pcJ1", "pcJ2"), ("pcE1", "pcE2"), ("ret 1 L0", "ret 2 L0"), ("AtE R b L c p len cp s ret 1", "AtE R b L c p len cp s ret 2"),
        ("stkBuf s 1", "stkBuf s 2"), ("424", "456"), ("(S.regs 11).toNat", "(S.regs 2).toNat"),
        ("opLen s p len 1", "opLen s p len 2"), ("opAvail s p len 1", "opAvail s p len 2"), ("opStart s p len 1", "opStart s p len 2"),
        ("(Nat.le_trans hnh (Nat.le_trans l1", "(Nat.le_trans hnh (Nat.le_trans l2"),
        ("  obtain ⟨hsl, hsl2⟩ := hslD.1 (Nat.le_refl _)", "  obtain ⟨hsl, hsl2⟩ := hslD.1 (by decide)\n  have hsl3 := hslD.2 (Nat.le_refl _)"),
        ("- 160", "- 192"), ("- 152", "- 184"), ("- 144", "- 176"), ("32 * 1", "32 * 2"),
        ("    · janus64_simp [hsl2]\n    · janus64_simp\n", "    · janus64_simp [hsl2]\n    · janus64_simp [hsl3]\n"),
        ("    rw [view_writeLE_out (hout.of_sub (buf_in_win (k := 552) (n := 8) hb' (by decide) (by decide)).1\n      (buf_in_win (k := 552) (n := 8) hb' (by decide) (by decide)).2)]",
         "    try rw [view_writeLE_out (hout.of_sub (buf_in_win (k := 552) (n := 8) hb' (by decide) (by decide)).1\n      (buf_in_win (k := 552) (n := 8) hb' (by decide) (by decide)).2)]"),
        ("      rw [beVal_writeLE_disj", "      try rw [beVal_writeLE_disj"),
        ("(show j = 0 by omega) with rfl\n    refine OpDone.transport (hop0 0 (by omega))",
         "(show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>\n    refine OpDone.transport (hop0 _ (by omega))"),
        ("(show j = 0 by omega) with rfl\n    refine OpDone.transport (hop 0 (by omega))",
         "(show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>\n    refine OpDone.transport (hop _ (by omega))"),
        ("    rcases (show i = 0 by omega) with rfl\n    simp only [opAt]\n    exact",
         "    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>\n    simp only [opAt] <;>\n    exact"),
        ("p.toNat + 96 + @A@ + i = p.toNat + (96 + @A@ + i)", "p.toNat + 96 + (@A@) + i = p.toNat + (96 + (@A@) + i)"),
        ("all_goals (simp only [opAt]; janus64_simp)", "all_goals (simp only [opAt]; try janus64_simp)"),
        ("@H2@", H2), ("@A@", f"{H0} + {H1}"),
    ]
    for x, y in R:
        t = t.replace(x, y)
    # parenthesise the start where it is an operand of `-` or `:=` targets
    t = t.replace(f"len.toNat - 96 - {H0} + {H1}", f"len.toNat - 96 - ({H0} + {H1})")
    t = t.replace(f"(st := {H0} + {H1})", f"(st := {H0} + {H1})")
    open(f"{d}/RunDJ{kind}2.lean", "w").write(t)
for k in (sys.argv[1:] or ["S", "F", "Z"]):
    conv(k)
print("ok")
