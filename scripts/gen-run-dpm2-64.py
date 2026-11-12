#!/usr/bin/env python3
"""gen-run-dpm2-64.py -- (agent top) generate lean/FvModexp/Proofs/Amd64/Top/RunD{P,M}2.lean (modulus operand, padded:
D2 -> J2 via the stack buffer / makeslice) from the exponent-operand files RunD{P,M}1.lean by substitution."""
import os, re, sys
d = os.path.dirname(os.path.abspath(__file__)) + "/../lean/FvModexp/Proofs/Amd64/Top"
H0, H1, H2 = "hdrV s p len 0", "hdrV s p len 1", "hdrV s p len 2"
def conv(kind):
    t = open(f"{d}/RunD{kind}1.lean").read()
    a = t.index("  have hst : min"); b = t.index("  have hst63")
    t = t[:a] + """  have hst : min (@H0@ + @H1@) (len.toNat - 96) ≤ len.toNat - 96 := Nat.min_le_right _ _
  have hdl48 : len.toNat - 96 < 2 ^ 48 := by omega
  have hcp63 : (BitVec.ofNat 64 (cp.toNat - inOff len)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hcpk : len.toNat - 96 ≤ cp.toNat - inOff len := by unfold inOff; split <;> omega
  have hz1' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 192) 8 = 0 := by
    rw [show (s.regs 4).toNat - 192 = (s.regs 4).toNat - 136 - 32 * 2 + 8 by omega]; exact hz1
  have hz2' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 184) 8 = 0 := by
    rw [show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 136 - 32 * 2 + 16 by omega]; exact hz2
  have hz3' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 176) 8 = 0 := by
    rw [show (s.regs 4).toNat - 176 = (s.regs 4).toNat - 136 - 32 * 2 + 24 by omega]; exact hz3
  have hR9 : (if len.toNat - 96 < @H0@ + @H1@ then BitVec.ofNat 64 (len.toNat - 96)
      else BitVec.ofNat 64 (@H0@ + @H1@)) = BitVec.ofNat 64 (min (@H0@ + @H1@) (len.toNat - 96)) := by
    split <;> rename_i h
    · rw [Nat.min_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_left (Nat.le_of_not_lt h)]
  generalize hstv : min (@H0@ + @H1@) (len.toNat - 96) = st at hndir hst hR9
  have hadd : BitVec.ofNat 64 (@H2@) + BitVec.ofNat 64 st = BitVec.ofNat 64 (st + @H2@) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
""" + t[b:]
    R = [
        ("The exponent operand", "The modulus operand"),
        ("exponent operand", "modulus operand"),
        (f"theorem d{kind}1", f"theorem d{kind}2"),
        (H1, "@H2@"),
        (f"min ({H0}) (len.toNat - 96)", f"min ({H0} + {H1}) (len.toNat - 96)"),
        (f"len.toNat - 96 - {H0}", f"len.toNat - 96 - ({H0} + {H1})"),
        (f"opStart s p len 1 = {H0}", f"opStart s p len 2 = {H0} + {H1}"),
        ("opLen s p len 1", "opLen s p len 2"), ("opAvail s p len 1", "opAvail s p len 2"),
        ("stkBuf s 1", "stkBuf s 2"), ("ret 1 Lk", "ret 2 Lk"), ("ret 1 1 (cstD 1)", "ret 2 2 (cstD 2)"),
        ("pcD1", "pcD2"), ("pcJ1", "pcJ2"), ("424", "456"), ("(S2.regs 11).toNat", "(S2.regs 2).toNat"),
        ("cstE 1", "cstE 2"), ("cstD 1", "cstD 2"),
        ("  obtain ⟨hsl1, hsl2⟩ := hsl.1 (Nat.le_refl _)", "  obtain ⟨hsl1, hsl2⟩ := hsl.1 (by decide)\n  have hsl3 := hsl.2 (Nat.le_refl _)"),
        ("And.intro hsteq hstv", "hstv"), ("And.intro hsteq <| And.intro hstv", "And.intro hstv"),
        ("hcp48 hsteq hstv", "hcp48 hstv"), ("hcp48, hsteq, hstv", "hcp48, hstv"),
        ("hsl1, hsl2, hz1', hz2', hz3',", "s3, hsl1, hsl2, hsl3, hz1', hz2', hz3', hR9, hadd,"),
        ("neg_asr63_andB _ _ hcp63 hst63", "neg_asr63_andB' _ _ hcp63 hst63"),
        ("""    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
    · rw [hstv]; janus64_simp [hsl1]
    · rw [hstv]; janus64_simp [hsl2]""", """    refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩
    · janus64_simp [hsl1]
    · janus64_simp [hsl2]
    · janus64_simp [hsl3]"""),
        ("    rcases (show j = 0 by omega) with rfl\n    refine OpDone.transport (hop 0 (by omega))",
         "    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>\n    refine OpDone.transport (hop _ (by omega))"),
        ("    rcases (show i = 0 by omega) with rfl\n    simp only [opAt]\n    exact",
         "    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>\n    simp only [opAt] <;>\n    exact"),
        ("hokB _ l1", "hokB _ l2"), ("(Nat.mul_le_mul_left _ l1)", "(Nat.mul_le_mul_left _ l2)"),
        ("@H2@", H2), ("@H0@", H0), ("@H1@", H1),
    ]
    for x, y in R:
        t = t.replace(x, y)
    t = re.sub(r"\(hdir : .*\)\n", "", t)
    open(f"{d}/RunD{kind}2.lean", "w").write(t)
for k in (sys.argv[1:] or ["P", "M"]):
    conv(k)
print("ok")
