import FvModexp.Proofs.Arm64.Nat.RemDefs

set_option autoImplicit false

/-!
# `nat.rem` (arm64): `(*stack).nat`'s precondition at `CALL (*stack).nat` (pure)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NatRem

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

/-- the callee's call environment one frame (`f` bytes) down (asm's `DivRec.callEnv_shift`, Arm64/Nat/DrsPathB.lean) -/
theorem callEnv_shift {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W ab))
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hg : S1.regs 28 = s.regs 28) (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 + 8 ≤ f) (hab : 8 ≤ ab) (hf16 : f % 16 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  unfold Apart at hga
  have hgr' : S1.mem.readLE ((S1.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hF1.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hF1.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact dataLoaded_win hdl hreg hro hF1 hw (by
      intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sn_pre {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl vc : Nat} {s P : State}
    (hpre : Pre R b cd L zp zl zc st up ul uc vp vl s) (hP : AtNat s P zp zl zc st up ul uc vp vl vc) :
    StackNat.Pre R b L 4208 24 st (kq ul vl) P := by
  obtain ⟨⟨⟨hce, hsv, -, -, -, -, -, hins, hsok, hsw, hsg, harr, -, hneed, hwba, hwbs, hfree, -, -, -, hcst, hinv⟩, -⟩, -⟩ :=
    hpre
  have hu := (hins up ul (by simp)).2.1
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce'
  have hsp : P.sp.toNat = s.sp.toNat - 208 := by
    rw [hP.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF := hP.fr
  have hFw : MemFrame s.mem P.mem (R.rt ++ winA s 41712 112) := hF.mono fun a n ho => by
    simp only [outside_append, winA, fw, outside_cons, outside_nil, and_true] at ho ⊢; omega
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 88 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [fw, outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have eW : stW P.mem st = stW s.mem st := hrd _ _ (by omega)
  have eL : stLen P.mem st = stLen s.mem st := hrd _ _ (by omega)
  have eC : stCap P.mem st = stCap s.mem st := hrd _ _ (by omega)
  have e28 := hP.r28
  refine ⟨callEnv_shift hce hLs hFw hsp e28 hP.reg (by omega) (by omega) (by omega) (by omega), hsv, ?ok, ?sw, ?arr,
    by simp only [kq]; omega, by rw [eL]; simp only [need, kq] at hneed ⊢; omega, ?cost, ?inv,
    by rw [hacc]; exact hwba, hwbs, by rw [eW, eL, eC]; exact hfree⟩
  case ok =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hsok
    refine ⟨a1, a2, by rw [hacc]; exact a3, a4, ?_, by rw [eL, eC]; exact a6, by rw [eC]; exact a7⟩
    show NatLive P.mem R L (stW P.mem st) (stCap P.mem st)
    rw [eW, eC]; intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hacc]; exact b3, b4⟩
  case sw => simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  case arr =>
    rw [eW, eC, e28]; intro h0
    obtain ⟨h1, h2⟩ := harr h0
    simp only [win, outside_cons, outside_nil, and_true] at h1 ⊢
    exact ⟨by rw [hsp]; omega, h2⟩
  case cost => rw [eL]; simp only [cost] at hcst; omega
  case inv =>
    rw [e28]
    refine RtInv.inv_frame' hF (fun r hr => ?_) hinv
    simp only [fw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by simp only; omega) (by simp only; omega))

end FvModexp.Arm64.NatRem
