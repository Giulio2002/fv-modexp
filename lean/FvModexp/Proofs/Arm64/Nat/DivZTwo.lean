import FvModexp.Proofs.Arm64.Nat.DivMLessA

set_option autoImplicit false

/-!
# `nat.div` (arm64), empty-tolerant dividend (`ExpSlow.DivHypLG`, asm s35), `len v ≥ 2`: the `cmp` call for any `z`

`two2Z` = `two2M` (DivMLess, `z = nil`) from the facts it uses: the call environment, `u` as `RdIn0`, `v` as `RdIn`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- at `nat.cmp`'s entry: the call, then `AtC` (= `two2M` from the facts it uses, any `z`) -/
theorem two2Z (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c up ul uc vp vl vc : BitVec 64) (s : State)
    (hce : CallEnv R L s 41504 112) (hui : ExpHyp.RdIn0 R L s 41504 112 up.toNat ul.toNat)
    (hvo : ExpHyp.RdIn R L s 41504 112 vp.toNat vl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 cmpE) (hsp : X.sp = s.sp - 240#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 248#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 retC) (hr0 : X.regs 0 = up) (hr1 : X.regs 1 = ul) (hr2 : X.regs 2 = uc)
    (hr3 : X.regs 3 = vp) (hr4 : X.regs 4 = vl) (hr5 : X.regs 5 = vc)
    (hF : MemFrame s.mem X.mem (proW s)) (hreg : X.mem.regions = s.mem.regions)
    (m1 : X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (m2 : X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat)
    (s1 : X.mem.readLE (s.sp.toNat + 8) 8 = zp.toNat) (s2 : X.mem.readLE (s.sp.toNat + 16) 8 = zl.toNat)
    (s3 : X.mem.readLE (s.sp.toNat + 24) 8 = zc.toNat) (s4 : X.mem.readLE (s.sp.toNat + 32) 8 = st.toNat)
    (s5 : X.mem.readLE (s.sp.toNat + 40) 8 = z2.toNat) (s6 : X.mem.readLE (s.sp.toNat + 48) 8 = z2l.toNat)
    (s7 : X.mem.readLE (s.sp.toNat + 56) 8 = z2c.toNat) (s8 : X.mem.readLE (s.sp.toNat + 64) 8 = up.toNat)
    (s9 : X.mem.readLE (s.sp.toNat + 72) 8 = ul.toNat) (s10 : X.mem.readLE (s.sp.toNat + 80) 8 = uc.toNat)
    (s11 : X.mem.readLE (s.sp.toNat + 88) 8 = vp.toNat) (s12 : X.mem.readLE (s.sp.toNat + 96) 8 = vl.toNat)
    (s13 : X.mem.readLE (s.sp.toNat + 104) 8 = vc.toNat) (Q : State → Prop)
    (k : ∀ S, AtC zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat uc.toNat
      vp.toNat vl.toNat vc.toNat s S → ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, hga, -, -, -⟩ := id hce
  unfold Apart at hga
  obtain ⟨-, hvacc, hv48, -, hvw⟩ := hvo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hspn : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have hpre' : CmpSum.Pre X := by
    unfold CmpSum.Pre GuardOK StackOK CmpSum.SliceOK
    rw [h30, h28, hr0, hr1, hr3, hr4, hspn, hrd _ _ (by omega)]
    refine ⟨by decide, by decide, ⟨hg1, by rw [hF.accessible]; exact hg2, by omega⟩,
      ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_⟩
    · rw [hF.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · by_cases h0 : ul.toNat = 0
      · exact Or.inl h0
      · obtain ⟨-, huacc, hu48, -, huw⟩ := hui.2 (by omega)
        simp only [win, outside_cons, outside_nil, and_true] at huw
        exact Or.inr ⟨by rw [hF.accessible]; exact huacc, by unfold Apart; omega⟩
    · exact Or.inr ⟨by rw [hF.accessible]; exact hvacc, by unfold Apart; omega⟩
  refine ReachesRet.call_regions (csum impl hap) hpc hpre' fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  rw [hspn] at hf
  have hslot : ∀ a, (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 112) →
      m.readLE a 8 = X.mem.readLE a 8 := fun a h =>
    hf.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hU : X.mem.readLE up.toNat (8 * ul.toNat) = s.mem.readLE up.toNat (8 * ul.toNat) := by
    by_cases h0 : ul.toNat = 0
    · simp only [h0, Nat.mul_zero, Memory.readLE_zero]
    · obtain ⟨-, -, -, -, huw⟩ := hui.2 (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at huw
      exact hrd _ _ (by omega)
  have hV : X.mem.readLE vp.toNat (8 * vl.toNat) = s.mem.readLE vp.toNat (8 * vl.toNat) := hrd _ _ (by omega)
  refine k _
    { pc := by rw [h30]
      sp := by rw [← hsp]
      r28 := by simp [setReg]; exact h28
      r29 := by simp [setReg]; exact h29
      r18 := by simp [setReg]; exact h18
      r0 := by
        simp [setReg]
        rw [hr1, hr4, hr0, hr3]
        show CmpSum.cmpRes _ _ (X.mem.readLE up.toNat (8 * ul.toNat)) (X.mem.readLE vp.toNat (8 * vl.toNat)) = _
        rw [hU, hV]
      mf := hF.trans hf fun a n h => ⟨by simp only [winA, proW, outside_cons, outside_nil, and_true] at h ⊢; omega,
        by simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
      reg := by rw [hrg, hreg]
      lr := by rw [hslot _ (Or.inl ⟨by omega, by omega⟩)]; exact m1
      fp := by rw [hslot _ (Or.inl ⟨by omega, by omega⟩)]; exact m2
      s1 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s1
      s2 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s2
      s3 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s3
      s4 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s4
      s5 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s5
      s6 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s6
      s7 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s7
      s8 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s8
      s9 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s9
      s10 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s10
      s11 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s11
      s12 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s12
      s13 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact s13 }

end FvModexp.Arm64.NatDiv
