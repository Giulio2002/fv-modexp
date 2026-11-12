import FvModexp.Proofs.Arm64.Exp.EvMiP
import FvModexp.Proofs.Arm64.Exp.EvMulD
import FvModexp.Proofs.Arm64.Exp.EvSm

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): stack callees with a possibly EMPTY destination; `StkX` at a callee (agent infra)

* `memFrame_drop_mid` / `liveFrame_drop_mid`: an empty range `(p, e)`, `e ≤ p`, anywhere in a frame list is dropped.
* `frmS_dst`: the frames of a STACK callee writing its window and `[pd, pd + 8 cd)` in the `stepC0` form: a located
  destination as it is; an EMPTY one (`cd = 0`) replaced by `(0, 0)` (always apart, LESSON s33).
* `ev_stkX`: divmc's `StkX` at a callee entry (`SP = sp`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

theorem memFrame_drop_mid {m m' : Memory} {A B : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : MemFrame m m' (A ++ [(p, e)] ++ B)) : MemFrame m m' (A ++ B) :=
  ⟨fun a n ho => Memory.readLE_congr (fun i hi => by
      rw [outside_append] at ho
      have := h.readLE (a + i) 1 (by
        rw [outside_append, outside_append]
        refine ⟨⟨ho.1.of_sub (by omega) (by omega), ?_⟩, ho.2.of_sub (by omega) (by omega)⟩
        simp only [outside_cons, outside_nil, and_true]; omega)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm), h.accessible⟩

theorem liveFrame_drop_mid {m m' : Memory} {L B : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : LiveFrame m m' L ([(p, e)] ++ B)) : LiveFrame m m' L B :=
  ⟨fun a n hin ho => Memory.readLE_congr (fun i hi => by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := h.readLE (a + i) 1 ⟨r, hr, by omega, by omega⟩ (by
        rw [outside_append]
        refine ⟨?_, ho.of_sub (by omega) (by omega)⟩
        simp only [outside_cons, outside_nil, and_true]; omega)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm)⟩

theorem out_zero (xs : List (Nat × Nat)) : Outside 0 0 xs := by
  induction xs with
  | nil => exact trivial
  | cons r rs ih => obtain ⟨lo, hi⟩ := r; exact ⟨Or.inl (Nat.zero_le _), ih⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- the frames of a stack callee writing its window `cw` and `[pd, pd + 8 cd)` in the `stepC0` form (see the doc) -/
theorem frmS_dst (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {pd ld cd vd : Nat} (hd : LN R L s.mem st M L1 pd ld cd vd) {M' : Memory}
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 128)
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) :
    ∃ qd kd : Nat, (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      Apart qd (8 * kd) (sp - K) (K + 448) ∧
      MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      (∀ q c, 0 < c → (0 < cd → Apart q (8 * c) pd (8 * cd)) → Apart q (8 * c) qd (8 * kd)) := by
  rcases Nat.eq_zero_or_pos cd with c0 | c0
  · subst c0
    have hF0 := memFrame_drop_mid (A := R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)]) (by omega) hF
    have hL0 := liveFrame_drop_mid (by omega) hLF
    refine ⟨0, 0, fun _ _ _ _ => out_00, fun _ _ _ _ => out_00, by unfold Apart; omega,
      hF0.mono fun a n ho => ?_, Expmc.liveFrame_widen hL0 fun a n ho => ?_, fun _ _ _ _ => by unfold Apart; omega⟩
    · rw [outside_append, outside_append] at ho
      rw [outside_append]; exact ⟨ho.1.1, ho.2⟩
    · rw [outside_append] at ho; exact ho.2
  · have hloc := (hd.1.2.2 c0).1
    obtain ⟨w1, -, -, -⟩ := Loc.ap hP hloc
    exact ⟨pd, cd, Loc.sub hloc, Loc.subL hloc, w1, hF, hLF, fun _ _ hc h => h c0⟩

set_option maxRecDepth 20000 in
/-- divmc's `StkX` at a callee entry `S'` (`SP = sp`, window `[sp - stk, sp + above)` inside ours) -/
theorem ev_stkX (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {S' : State} (hsN : S'.sp.toNat = sp) (hgN : (S'.regs 28).toNat = g) (fm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 88) : StkX R L1 S' stk above st := by
  obtain ⟨x1, x2, x3, x4, x5, x6, -⟩ := miStk hP hw
  have hsi := hw.stkIn hP hsN hgN fm hstk habove
  have hok := hw.sok
  subst fm
  refine ⟨x1, x2, ?_, ?_, ?_, x4, x3, x5⟩
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with c0 | c0
    · have hl0 : stLen S'.mem st = 0 := by have := hok.2.2.2.2.2.1; omega
      simp only [frP, frN, c0, x6 c0, hl0, Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
      exact Or.inr (out_zero R.rt)
    · exact (hok.2.2.2.2.1 c0).2.1.sub (by simp only [frP]; omega)
        (by simp only [frP, frN]; have := hok.2.2.2.2.2.1; omega)
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with c0 | c0
    · have hl0 : stLen S'.mem st = 0 := by have := hok.2.2.2.2.2.1; omega
      simp only [frP, frN, c0, x6 c0, hl0, Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
      exact out_zero _
    · exact (hsi.2.2.2 c0).1.of_sub (by simp only [frP]; omega)
        (by simp only [frP, frN]; have := hok.2.2.2.2.2.1; omega)
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with c0 | c0
    · have hl0 : stLen S'.mem st = 0 := by have := hok.2.2.2.2.2.1; omega
      simp only [frP, frN, c0, x6 c0, hl0, Nat.zero_sub, Nat.mul_zero]
      unfold Apart; omega
    · have := (hsi.2.2.2 c0).2
      have := hok.2.2.2.2.2.1
      simp only [frP, frN]; unfold Apart at *; omega

end

end FvModexp.Arm64.ExpEven
