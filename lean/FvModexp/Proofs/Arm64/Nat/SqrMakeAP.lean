import FvModexp.Proofs.Arm64.Nat.SqrMakeAD
import FvModexp.Proofs.Arm64.Nat.StackNatCall

set_option autoImplicit false

/-!
# `nat.sqr` (arm64), `make_alloc`: `makeslice(Word, 2n, 2n + 4)`'s precondition at its entry (`AA`)
(adapted from MulMakeAP)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem sq_wordT_eq : NatAdd.wordT = StackNat.wT := rfl

set_option maxRecDepth 20000 in
theorem mk_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s S : State}
    {st' xp' xl' xc' : BitVec 64}
    (hpre : SPre R b L W zp zc st xp xl xc s) (hx : 2 ≤ xl)
    (hA : AA s S W st' xp' xl' xc') (exl : xl'.toNat = xl) :
    (MakeslicePre 4096 S ∧ StackRoom S 4096 3 ∧
      LiveAt R (cA "runtime.makeslice") [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat] L b (makesliceRound S)
        (S.regs 28).toNat S.mem (calleeStack S 4096 3)) ∧
      0 < typSize S.mem (S.regs 0).toNat * (S.regs 2).toNat := by
  obtain ⟨hce, hsw, hsv, -, -, -, -, hxl12, -, -, -, -, -, -, -, -, -, -, -, hcost, hinv⟩ := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, hr30, hr0, hr1, hr2, hsp, hg, -, -, -, -, -, -, -, -, -, -, hF0, -⟩ := hA
  rw [exl] at hr1 hr2
  have hsp' : S.sp.toNat = s.sp.toNat - 176 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hwT : Apart StackNat.wT 16 (s.sp.toNat - W) (W + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hga hwT
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts hd
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3 hwT
  have e0 : (S.regs 0).toNat = 2641088 := by rw [hr0, sq_wordT_eq, hwTv]; rfl
  have e1 : (S.regs 1).toNat = 2 * xl := by rw [hr1, BitVec.toNat_ofNat]; omega
  have e2 : (S.regs 2).toNat = 2 * xl + 4 := by rw [hr2, BitVec.toNat_ofNat]; omega
  have hFw : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - W, s.sp.toNat + 64)]) := hF0.mono fun a k h => by
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hts : typSize S.mem (S.regs 0).toNat = 8 := by
    simp only [typSize, e0]; rw [hF0.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)]
    exact ht1
  have htn : typNoscan S.mem (S.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, e0]
    rw [hF0.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega), ht2]; rfl
  have hround : makesliceRound S = blockSize (8 * (2 * xl + 4)) true := by
    simp only [makesliceRound, hts, htn, e2]
  have hbl := blockSize_le_allocCost (8 * (2 * xl + 4)) true
  have hmc2 : makeB (2 * xl) ≤ sqrC (stLen s.mem st) xl := by unfold sqrC; omega
  have hmc : makeB (2 * xl) = allocCost (8 * (2 * xl + 4)) := rfl
  have hgo : Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - W, s.sp.toNat + 64) :: R.rt) := by
    simp only [outside_cons]; exact ⟨by omega, hgr⟩
  have hc := call_pre R L b (makesliceRound S) (cA "runtime.makeslice")
    [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat]
    (s := s) (S := S) (lo := s.sp.toNat - W) (hi := s.sp.toNat + 64) (stack := 4096) (nargs := 3) (fr := 176)
    hg1 hg2 (by omega) hgo hFw (by rw [hg]) (by omega) (by omega) (by rw [hr30]; decide) (by rw [hr30]; decide)
    (by decide) (by omega) (by omega) (by omega) (by omega)
    (by rw [show s.sp.toNat + 64 - (s.sp.toNat - W) = W + 64 by omega]; exact hw)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show s.sp.toNat + 64 - (s.sp.toNat - W) = W + 64 by omega]; exact hout)
    (by simp only [LiveSep, win] at hLs ⊢; exact hLs)
    (by rw [e0, e1, e2]; rw [← hwTv, ← sq_wordT_eq]; exact hsv.1 _ _ _ (by omega))
    (by rw [hg]; exact inv_frame_winA hF0 hout (by omega) (by decide) hinv)
    (by rw [hround]; omega)
  refine ⟨⟨⟨hc.1, ⟨by rw [e0]; omega, by rw [e0, hF0.accessible]; exact ht3⟩, by omega, by omega, ?_, ?_⟩, hc.2⟩, ?_⟩
  · rw [hts, e2]; unfold maxAlloc; omega
  · rw [e0]; simp only [calleeStack, outside_cons, outside_nil, and_true]; omega
  · rw [hts, e2]; omega

set_option maxRecDepth 20000 in
/-- the type facts of `Word`'s descriptor at the call: size 8, no pointers; `cap = 2n + 4` -/
theorem mk_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s S : State}
    {st' xp' xl' xc' : BitVec 64}
    (hpre : SPre R b L W zp zc st xp xl xc s) (hA : AA s S W st' xp' xl' xc') (exl : xl'.toNat = xl) :
    makesliceRound S = blockSize (8 * (2 * xl + 4)) true ∧
      typSize S.mem (S.regs 0).toNat * (S.regs 2).toNat = 8 * (2 * xl + 4) ∧
      typNoscan S.mem (S.regs 0).toNat = true := by
  obtain ⟨hce, hsw, -, -, -, -, -, hxl12, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, hd, -, -, -, -, -⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, -, hr0, -, hr2, -, -, -, -, -, -, -, -, -, -, -, -, hF0, -⟩ := hA
  rw [exl] at hr2
  have hwT : Apart StackNat.wT 16 (s.sp.toNat - W) (W + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwT
  obtain ⟨ht1, ht2, -⟩ := StackNat.wT_facts hd
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 hwT
  have e0 : (S.regs 0).toNat = 2641088 := by rw [hr0, sq_wordT_eq, hwTv]; rfl
  have e2 : (S.regs 2).toNat = 2 * xl + 4 := by rw [hr2, BitVec.toNat_ofNat]; omega
  have hts : typSize S.mem (S.regs 0).toNat = 8 := by
    simp only [typSize, e0]; rw [hF0.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)]
    exact ht1
  have htn : typNoscan S.mem (S.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, e0]
    rw [hF0.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega), ht2]; rfl
  refine ⟨by simp only [makesliceRound, hts, htn, e2], by rw [hts, e2], htn⟩

end FvModexp.Arm64.NatSqr
