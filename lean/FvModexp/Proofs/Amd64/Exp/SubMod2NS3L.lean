import FvModexp.Proofs.Amd64.Exp.SubMod2NCall

/-!
# `nat.subMod2N` (amd64): `J2` (x' < y'): `z = z.sub(y', x')` → `J3` (agent infra)

Small-context lemma (abstract state `S2` at the `nat.sub` entry, `RSP = e - 136`): the caller's run only discharges
register / frame equations of the literal state.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at the `nat.sub` entry of the `x' < y'` branch (`z.sub(y', x')`, return address `+0x2ac`) -/
theorem s3lt (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hsub : SubHypR impl R) {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {l1 p2 l2 c2 : Nat} {L2 : List (Nat × Nat)} {b2 : Nat}
    (S2 : State) (hpc : S2.rip = BitVec.ofNat 64 6183136) (hsp : (S2.regs 4).toNat = (s.regs 4).toNat - 136)
    (hrd : S2.mem.readLE (S2.regs 4).toNat 8 = 6216524) (h14 : S2.regs 14 = s.regs 14) (hfs : S2.fsBase = s.fsBase)
    (hx15 : S2.xmm 15 = 0) (hdf : S2.df = false)
    (h0 : S2.regs 0 = BitVec.ofNat 64 zp) (h3 : S2.regs 3 = BitVec.ofNat 64 zl) (h1 : S2.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S2.regs 7 = BitVec.ofNat 64 p2) (h6 : S2.regs 6 = BitVec.ofNat 64 l2) (h8 : S2.regs 8 = BitVec.ofNat 64 c2)
    (h9 : S2.regs 9 = BitVec.ofNat 64 zp) (h10 : S2.regs 10 = BitVec.ofNat 64 l1) (h11 : S2.regs 11 = BitVec.ofNat 64 zc)
    (hrt : Rt R b L s zp zc n 2 S2.mem L2 b2) (hfw : Fw s S2.mem zp zl zc yp n)
    (hv1 : natVal S2.mem zp l1 = natVal s.mem zp zl % 2 ^ n) (hn1 : NatNorm S2.mem zp l1) (hW1 : l1 ≤ W n)
    (hv2 : natVal S2.mem p2 l2 = natVal s.mem yp yl % 2 ^ n) (hn2 : NatNorm S2.mem p2 l2) (hW2 : l2 ≤ W n)
    (hlc2 : l2 ≤ c2) (hc2 : c2 < 2 ^ 40) (hlc1 : l1 ≤ zc)
    (hacc1 : S2.mem.accessible zp (8 * l1) false = true) (hacc2 : S2.mem.accessible p2 (8 * l2) false = true)
    (h482 : p2 + 8 * l2 ≤ 2 ^ 48) (hh2 : Held R L2 p2 (8 * l2))
    (hw2 : p2 + 8 * l2 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ p2) (hzp2 : Apart zp (8 * zc) p2 (8 * l2))
    (k3 : J3 impl R b L op zp zl zc yp yl yc n s)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n) :
    Goal impl R b L zp zl zc yp yl n s S2 := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, hn1', -, hzl, hW, hzc, -, -,
    -, -, hzlive, hzw, -⟩ := id hpre
  have hent := ent_of hpre
  simp only [W] at hW hW1 hW2
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hs4 : 4576 ≤ (s.regs 4).toNat := by omega
  have hzh1 : Held R L2 zp (8 * l1) := ((hrt.2.2.2.2.2.2 (by omega)).2.1).sub (Nat.le_refl _) (by omega)
  have hll : l1 ≤ l2 := by
    rcases (SubMod2N.cmp_lt_iff S2.mem zp l1 p2 l2 hn1 hn2).2 (by rw [hv1, hv2]; exact hlt) with h | ⟨h, -⟩ <;> omega
  refine subCall hap hsub (zp := zp) (zl := zl) (zc := zc) (xp := p2) (xl := l2) (xc := c2) (yp := zp) (yl := l1)
    (yc := zc) (sp' := (s.regs 4).toNat - 136) (g := (s.regs 14).toNat) (ra := 6216524) (M := S2.mem)
    (bx39 := by omega)
    (ra_of hap (by decide) 0x2ac (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hpc hrd h0 h3 h1 h7 h6 h8 h9 h10 h11 hx15 hdf rfl hsp (by rw [h14])
    (subPre_of hpre hrt rfl hsp h14 hfs (by omega) (by rw [hv1, hv2]; omega) hlc2 (by omega) hc2 hzc hW2 (Or.inr hzp2)
      (Or.inl rfl) hacc2 h482 hh2 hn2 (by omega) hacc1 (by omega) hzh1 hn1 (by omega))
    fun s'' p' n' c' L3 b3 hpc'' hsp'' h14'' hx'' hfs'' hdf'' hrg'' e0 e1 e2 hv hnorm hlc hln hLE hb3 hinv3 hlive3
      hor3 hF3 hLF3 hreuse hc40 => ?_
  obtain ⟨rfl, rfl⟩ := hreuse (by omega)
  refine k3 s'' n' L3 b3 hpre hpc'' ?_ ⟨h14''.trans h14, hfs''.trans hfs, hx''.trans (hx15.trans hent.2.2.2.1.symm),
      hdf''.trans hdf⟩ e0 e1 e2 (fw_call hs4 hout hzw (Or.inl rfl) (by omega) (by omega) hfw hF3)
    (rt_call hrt hs4 (by omega) (by omega) (Or.inl rfl) hrg'' hF3 hLF3 hLE hb3 (makeCost_le_w (by simp only [W]; omega))
      hinv3 hlive3) hlt (by rw [hv, hv1, hv2]) hnorm (by simp only [W]; omega)
  rw [hsp'']; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

end FvModexp.Amd64.SubMod2N
