import FvModexp.Proofs.Arm64.Exp.P2W2Tail
import FvModexp.Proofs.Arm64.Exp.P2W2WC
import FvModexp.Proofs.Arm64.Exp.NHyp

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the function's post `FQ` from the tail (agent infra)

`FQ` = the ABI facts (`SP`, `R18`, `g`, `FP` restored) and `NHyp.CPost` (window `[SP - (K + 464), SP + 96)`).
`finQ`: from `WC` at the tail's memory `M` (any stack level), a result nat in the `NatOF` form and `TPost`
(the closure restored `len = len₀`), the post holds.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.ExpHyp

/-- the function's post -/
@[reducible] def FQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K zp zc st v cst : Nat) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    NHyp.CPost R b L (K + 464) 96 zp zc st v cst s s'

/-- the tail's writes -/
@[reducible] def TW (sp st : Nat) : List (Nat × Nat) :=
  [(sp - 24, sp - 8), (sp + 95, sp + 96), (sp + 256, sp + 280), (st + 8, st + 16)]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a result nat (`NatOF`) with a non-empty array is apart from the window and the stack header -/
theorem res_apart (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) (hc : 0 < c) :
    Apart p (8 * c) (sp - K) (K + 560) ∧ Apart p (8 * c) st 24 := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
  · obtain ⟨⟨-, h2, h3, -⟩, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc
    exact ⟨h2, h3⟩
  · refine ⟨hin.apart hP.win_rt |>.symm, ?_⟩
    rcases hP.stk0.2.1 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart; omega
    · exact (hin.apart hO).symm

theorem res_bytes (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {p c : Nat}
    (hr : (p = zp ∧ c = zc) ∨ (1 ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) :
    ∀ i, i < 8 * c → Outside (p + i) 1 (TW sp st) := by
  intro i hi
  have hK := hP.1.2.2.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := res_apart hP hr (by omega)
  unfold Apart at h1 h2
  simp only [TW, outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 20000 in
/-- **the function's post** from the tail -/
theorem finQ (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p l c v cst : Nat} (hres : NatOF R L L1 M zp zc 1 p l c v) (hb : b - cst ≤ b1) {s' : State}
    (ht : TPost sp g st (stLen s.mem st) p l c (s.regs 18) (s.regs 29) M s') :
    FQ R b L K zp zc st v cst s s' := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, tF⟩ := ht
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp := hP.1.sp
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a n, (∀ i, i < n → Outside (a + i) 1 (TW sp st)) → s'.mem.readLE a n = M.readLE a n :=
    fun a n h => FvModexp.Arm64.P2W2.MemFrame.bytewise tF h
  have hhd : ∀ a n, st ≤ a → a + n ≤ st + 8 ∨ st + 16 ≤ a ∧ a + n ≤ st + 24 → s'.mem.readLE a n = M.readLE a n := by
    intro a n h1 h2
    refine tF.readLE a n ?_
    simp only [TW, outside_cons, outside_nil, and_true]; omega
  have e0 : stW s'.mem st = stW M st := hhd _ _ (Nat.le_refl _) (Or.inl (by omega))
  have e2 : stCap s'.mem st = stCap M st := hhd _ _ (by omega) (Or.inr ⟨by omega, by omega⟩)
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hres
  have hby := res_bytes hP v6
  have hokM := hw.sok
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := hokM
  have hlen := hw.len
  have hlo := hw.lo
  refine ⟨t1.trans hP.1.1.symm, t2, t3.trans hP.1.2.1.symm, t4, p, l, c, t5, t6, t7, L1, b1, ?nat,
    ⟨hw.le, hb, ?inv⟩, ⟨⟨?sok, t8, ?kf⟩, hw.ain.congr e0 e2 fun _ hr => hr⟩, ?fr, ?lf⟩
  case nat =>
    refine ⟨?_, ?_, v3, v4, fun hc => ?_, v6⟩
    · rw [← v1]; exact hrd _ _ fun i hi => hby i (by omega)
    · rcases v2 with h | h
      · exact Or.inl h
      · rcases Nat.eq_zero_or_pos l with h0 | hl0
        · exact Or.inl h0
        right
        rw [hrd _ _ fun i hi => by rw [Nat.add_assoc]; exact hby (8 * (l - 1) + i) (by omega)]; exact h
    · obtain ⟨q1, q2, q3, q4⟩ := v5 hc
      exact ⟨q1, q2, by rw [tF.accessible]; exact q3, q4⟩
  case inv =>
    rw [hP.1.g]
    refine Expmc.inv_frame tF (fun r hr => ?_) hw.inv
    simp only [TW, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inr (hout.of_sub (by omega) (by omega))
      | exact hh.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega))
  case sok =>
    refine ⟨h8, hh, by rw [tF.accessible]; exact hacc, h48, ?_, by show s'.mem.readLE (st + 8) 8 ≤ _; rw [t8, e2]; omega, by rw [e2]; exact hc40⟩
    rw [e0, e2]
    intro hc
    obtain ⟨q1, q2, q3, q4⟩ := hlive hc
    exact ⟨q1, q2, by rw [tF.accessible]; exact q3, q4⟩
  case kf =>
    rcases hw.kf with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨e0.trans a1, e2.trans a2⟩
    · exact Or.inr (by rw [e0, e2]; exact ⟨a1, a2⟩)
  case fr =>
    have hwin : winA s (K + 464) 96 = WN sp K := by
      simp only [winA, WN, hsp]
      rw [show sp + 464 - (K + 464) = sp - K by omega, show sp + 464 - 8 = sp + 456 by omega,
        show sp + 464 + 8 = sp + 472 by omega, show sp + 464 + 96 = sp + 560 by omega]
    rw [hwin, show stWs s.mem st = stkWs s.mem st from rfl, List.append_assoc, List.append_assoc,
      ← List.append_assoc (WN sp K)]
    refine hw.fr.trans tF fun a n ho => ⟨by rw [List.append_assoc]; exact ho, ?_⟩
    simp only [WN, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
    simp only [TW, outside_cons, outside_nil, and_true]
    omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [tF.readLE a n ?_, hw.lf.readLE a n hin ho]
    obtain ⟨r0, hr0, q1, q2⟩ := hin
    have := hLs r0 hr0
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at this ho
    simp only [TW, outside_cons, outside_nil, and_true]
    omega

end

end FvModexp.Arm64.P2W2
