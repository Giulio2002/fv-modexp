import FvModexp.Proofs.Arm64.Exp.SubMod2NCall

/-!
# `nat.subMod2N` (arm64): `J2` → `x.cmp(y)` → `z.sub(x, y)` + return, or `z.sub(y, x)` → `J3` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem cmp_neg {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
    (hlt : natVal m p l1 < natVal m q l2) :
    CmpSum.cmpRes l1 l2 (m.readLE p (8 * l1)) (m.readLE q (8 * l2)) = 18446744073709551615#64 := by
  have := (SubMod2N.cmp_lt_iff m p l1 q l2 h1 h2).2 hlt
  unfold CmpSum.cmpRes natVal at *
  rcases this with h | ⟨rfl, h⟩
  · rw [ite_eq_left_iff.2 (fun h' => absurd h h')]
  · simp [h]

theorem cmp_nonneg {m : Memory} {p q l1 l2 : Nat} (h1 : NatNorm m p l1) (h2 : NatNorm m q l2)
    (hge : ¬ natVal m p l1 < natVal m q l2) :
    (CmpSum.cmpRes l1 l2 (m.readLE p (8 * l1)) (m.readLE q (8 * l2))).getLsbD 63 = false := by
  have h := mt (SubMod2N.cmp_lt_iff m p l1 q l2 h1 h2).1 hge
  unfold CmpSum.cmpRes natVal at *
  by_cases a : l1 < l2
  · exact absurd (Or.inl a) h
  rw [if_neg a]
  by_cases b' : l2 < l1
  · rw [if_pos b']; decide
  rw [if_neg b']
  have e : l1 = l2 := by omega
  rw [if_neg (fun c => h (Or.inr ⟨e, c⟩))]
  split <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- from the entry of `x'.cmp(y')` (`+0x1ec`) -/
theorem s3c (impl : List Segment) (hap : ImplApart Extracted.program impl) {R : RtInv} (hsub : SubHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (k3 : J3 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (S : State) {l1 p2 l2 c2 : Nat} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hpc : S.pc = BitVec.ofNat 64 1782608) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18) (h30 : S.regs 30 = BitVec.ofNat 64 (1805584 + 4 * 124))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 l1)
    (h3 : S.regs 3 = BitVec.ofNat 64 p2) (h4 : S.regs 4 = BitVec.ofNat 64 l2)
    (hfw : Fw s S.mem zp zl zc yp n) (r16 : S.mem.readLE (s.sp.toNat - 16) 8 = zp)
    (r40 : S.mem.readLE (s.sp.toNat - 40) 8 = l1) (r32 : S.mem.readLE (s.sp.toNat - 32) 8 = zc)
    (r24 : S.mem.readLE (s.sp.toNat - 24) 8 = p2) (r56 : S.mem.readLE (s.sp.toNat - 56) 8 = l2)
    (r48 : S.mem.readLE (s.sp.toNat - 48) 8 = c2) (hrt : Rt R b L s zp zc n 2 S.mem L2 b2)
    (hv1 : natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n) (hn1 : NatNorm S.mem zp l1) (hW1 : l1 ≤ W n)
    (hv2 : natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n) (hn2 : NatNorm S.mem p2 l2) (hW2 : l2 ≤ W n)
    (hlc2 : l2 ≤ c2) (hc2 : c2 < 2 ^ 40)
    (hacc2 : S.mem.accessible p2 (8 * l2) false = true) (h482 : p2 + 8 * l2 ≤ 2 ^ 48) (hh2 : Held R L2 p2 (8 * l2))
    (hw2 : p2 + 8 * l2 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ p2) (hzp2 : Apart zp (8 * zc) p2 (8 * l2)) :
    Goal impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -, -, -, -, -, hn1', -, hzl, hW, hzc, -, -,
    -, -, hzlive, hzw, hzg, -⟩ := id hpre
  simp only [W] at hW hW1 hW2
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw hg3 hga
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hzh : Held R L2 zp (8 * zc) := (hrt.2.2.2.2.2.2 (by omega)).2.1
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hacc1 : S.mem.accessible zp (8 * l1) false = true :=
    Memory.accessible_sub _ (hrt.2.2.2.2.2.2 (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hgv : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hrt.2.1.readLE _ _ ?_
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hzg hga
    exact ⟨⟨hgrt, by omega, by omega⟩, by omega⟩
  have tg : (S.regs 28).toNat = (s.regs 28).toNat := by rw [h28]
  refine cmpCall hpc (CmpW.pre_of (sp := s.sp.toNat - 144) (g := (s.regs 28).toNat) hsp
    (h28.trans (Expmc.bv_ofNat_toNat _).symm) h30 h0 h1 h3 h4 (by decide) (by decide) (by omega) (by omega) (by omega)
    (Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega)) hg1 (by rw [hrt.2.1.accessible]; exact hg2)
    (by rw [hgv]; omega) (Or.inr ⟨by omega, hacc1, by unfold Apart; omega⟩)
    (Or.inr ⟨by omega, hacc2, by unfold Apart; omega⟩)) fun S' hpc' hsp' hr0 h18' h28' h29' hF' hrg' => ?_
  rw [h0, h1, h3, h4, tN (show zp < 2 ^ 64 by omega), tN (show l1 < 2 ^ 64 by omega), tN (show p2 < 2 ^ 64 by omega),
    tN (show l2 < 2 ^ 64 by omega)] at hr0
  rw [hspT] at hF'
  sorry

end FvModexp.Arm64.SubMod2N
