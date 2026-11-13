import FvModexp.Proofs.Amd64.NatQ.DivCmp

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivCmpB.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64), `len v ≥ 2`: the `nat.cmp` call (`CmpSum.cmp_summary` on `LibDiv`) → `AtC`

Port of `Arm64/Nat/DivCmpB.lean`. `nat.cmp`'s frame (`CmpSum.frame` at `RSP = SP - 240`: `[SP - 248, SP - 240)`,
`[SP - 232, SP - 224)`, `[SP - 208, SP - 200)`) lies inside the window and apart from every slot `AtC` names.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem two2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (s : State)
    (hpre : Pre R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
    (X : State) (hX : AtK zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s X)
    (Q : State → Prop)
    (k : ∀ S, AtC zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s S →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q := by
  have hp := hpre.f
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hul, huacc, hu48, -, huw⟩ := hp.uo
  obtain ⟨hvl, hvacc, hv48, -, hvw⟩ := hp.vo
  simp only [win, outside_cons, outside_nil, and_true] at huw hvw
  have hF := hX.mf
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [hX.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have t0 : (X.regs 0).toNat = u := by rw [hX.a0, BitVec.toNat_ofNat]; omega
  have t3 : (X.regs 3).toNat = ul := by rw [hX.a3, BitVec.toNat_ofNat]; omega
  have t7 : (X.regs 7).toNat = v := by rw [hX.a7, BitVec.toNat_ofNat]; omega
  have t6 : (X.regs 6).toNat = vl := by rw [hX.a6, BitVec.toNat_ofNat]; omega
  have hpre' : CmpSum.Pre X := by
    unfold CmpSum.Pre CmpSum.SliceOK
    rw [t0, t3, t7, t6, hspn, show (s.regs 4).toNat - 240 = (s.regs 4).toNat - 240 from rfl, hX.rc]
    refine ⟨by decide, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · by_cases h0 : ul = 0
      · exact Or.inl h0
      · exact Or.inr ⟨by rw [hF.accessible]; exact huacc, by unfold Apart; omega⟩
    · exact Or.inr ⟨by rw [hF.accessible]; exact hvacc, by unfold Apart; omega⟩
  refine ReachesRet.call_regions (csum impl hap) hX.pc hpre' fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v6, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  rw [hspn] at hf
  have hslot : ∀ a n, (a + n ≤ (s.regs 4).toNat - 248 ∨ (s.regs 4).toNat - 200 ≤ a) →
      m.readLE a n = X.mem.readLE a n := fun a n h =>
    hf.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hU : X.mem.readLE u (8 * ul) = s.mem.readLE u (8 * ul) := by
    by_cases h0 : ul = 0
    · simp only [h0, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]
    · exact hrd _ _ (by omega)
  have hV : X.mem.readLE v (8 * vl) = s.mem.readLE v (8 * vl) := hrd _ _ (by omega)
  have hraS : X.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  refine k _
    { pc := by simp only [retAddrOf]; rw [hspn, hX.rc]
      sp := by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [hX.sp]; bv_omega
      r5 := by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hX.r5
      r14 := by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hX.r14
      fs := hX.fs
      x15 := hX.x15
      df := hX.df
      r0 := by
        simp only [setRegF_apply, ↓reduceIte]
        rw [t3, t6, t0, t7]
        show CmpSum.cmpRes _ _ (X.mem.readLE u (8 * ul)) (X.mem.readLE v (8 * vl)) = _
        rw [hU, hV]; rfl
      mf := hF.trans hf fun a n h => by simp only [win, proW, outside_cons, outside_nil, and_true] at h ⊢; omega
      reg := by rw [hrg, hX.reg]
      ra := by rw [hslot _ _ (by omega)]; exact hraS
      bp := by rw [hslot _ _ (by omega)]; exact hX.bp
      s1 := by rw [hslot _ _ (by omega)]; exact hX.s1
      s2 := by rw [hslot _ _ (by omega)]; exact hX.s2
      s3 := by rw [hslot _ _ (by omega)]; exact hX.s3
      s4 := by rw [hslot _ _ (by omega)]; exact hX.s4
      s5 := by rw [hslot _ _ (by omega)]; exact hX.s5
      s6 := by rw [hslot _ _ (by omega)]; exact hX.s6
      s7 := by rw [hslot _ _ (by omega)]; exact hX.s7
      s8 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.ru
      s9 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.rul
      s10 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.ruc
      s11 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.rv
      s12 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.rvl
      s13 := by rw [hslot _ _ (by omega), hF.readLE _ _ (by simp only [proW, outside_cons, outside_nil, and_true]; omega)]; exact hp.rvc
      q0 := by rw [hslot _ _ (by omega)]; exact hX.q0 }

end FvModexp.Amd64.Q.NatDiv
