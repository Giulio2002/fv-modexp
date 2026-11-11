import FvModexp.Proofs.Arm64.Exp.ModInvRnd
import FvModexp.Proofs.Arm64.Exp.ModInvJ2

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): callee preconditions inside a round (agent infra)

At a callee state `S'` (`SP' = SP - 240`, `X28` the entry's, memory `M` with the runtime facts `RtM`): the call
environment, `Globals`, the stack object, `x`, and the owned arrays as `RdIn` / `WrOut` / `StkApart` (pure lemmas),
and the assembled preconditions of `nat.sqr`, `nat.mul`, `nat.trunc`, `nat.lsh`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut LshPost)

section
variable {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

theorem sp'_eq {S' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) :
    S'.sp.toNat = s.sp.toNat - 240 := by
  rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)

set_option maxRecDepth 20000 in
theorem cenv_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) : CallEnv R L1 S' stk above := by
  have he := env_rt hpre hrt
  have hd := dl_rt hpre hrt
  have hro : RoOut R := hpre.1.2.2.2.2.2.2.2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := he
  exact CallW.callEnv_of ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, hd, hro⟩ hsp
    (by rw [h28, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hm hstk (by omega)

set_option maxRecDepth 20000 in
/-- `Globals` (window form) at a callee state `S'` (`SP' = SP - 240`, window `stk ≤ kc`, `above ≤ 88`) -/
theorem globals_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hsp : S'.sp.toNat = s.sp.toNat - 240)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) : RunIface.Globals R M (win S' stk above) := by
  have hK : 240 + kc ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simp only [K] at this; omega
  obtain ⟨-, -, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, -⟩ := hpre
  obtain ⟨-, hF, -⟩ := hrt
  have hrd : ∀ j, j + 8 ≤ 32 → M.readLE (RunIface.gA + j) 8 = s.mem.readLE (RunIface.gA + j) 8 := fun j hj =>
    hF.readLE _ _ (by
      simp only [outside_append] at g10 ⊢
      exact ⟨⟨⟨g9.of_sub (by omega) (by omega), g10.1.1.of_sub (by omega) (by omega)⟩,
        g10.1.2.of_sub (by omega) (by omega)⟩, g10.2.of_sub (by omega) (by omega)⟩)
  simp only [outside_append, winA, K, A, outside_cons, outside_nil, and_true] at g10 g13
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hF.accessible]; exact g8, g9, ?_,
    by rw [hF.accessible]; exact g11, g12, ?_⟩
  · rw [g5, hrd 8 (by omega), ← g5]; exact g1
  · rw [g6, hrd 16 (by omega), ← g6]; exact g2
  · rw [g7, hrd 24 (by omega), ← g7]; exact g3
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact g4
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; omega
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; omega

/-- an owned array (cap `> 0`) as a callee operand -/
theorem rdIn_own {L1 : List (Nat × Nat)} {M : Memory} {p c l : Nat}
    (h : Own R kc L L1 s zp zc st xp xl M p c) (hc : 0 < c) (hl : l ≤ c) (hK : 240 + kc ≤ s.sp.toNat) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 240) (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc)
    (habove : above ≤ 88) : RdIn R L1 S' stk above p l := by
  obtain ⟨h1, -, h3, -, h5, -, -, -⟩ := h
  obtain ⟨-, c2, c3, c4⟩ := h3 hc
  simp only [win, K, A, outside_cons, outside_nil, and_true] at h5
  simp only [RdIn, win, outside_cons, outside_nil, and_true]
  rw [hm, hsp]
  exact ⟨by omega, M.accessible_sub c3 (Or.inr rfl) (Nat.le_refl _) (by omega), by omega,
    c2.sub (Nat.le_refl _) (by omega), by omega⟩

/-- an owned array as a callee's output -/
theorem wrOut_own {L1 : List (Nat × Nat)} {M : Memory} {p c : Nat}
    (h : Own R kc L L1 s zp zc st xp xl M p c) (hK : 240 + kc ≤ s.sp.toNat) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 240) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ kc) (habove : above ≤ 88) : WrOut R L1 S' stk above p c := by
  obtain ⟨h1, -, h3, -, h5, h6, -, -⟩ := h
  simp only [win, K, A, outside_cons, outside_nil, and_true] at h5
  simp only [WrOut]
  rw [hm, h28]
  refine ⟨h1, h3, fun hc => ⟨?_, h6⟩⟩
  simp only [win, hsp, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- `x[:k]` as a callee operand -/
theorem rdIn_x (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {k : Nat} (hk : k ≤ xl) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 240) (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc)
    (habove : above ≤ 88) : RdIn R L1 S' stk above xp k := by
  obtain ⟨⟨-, ⟨-, hb', -, -⟩, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, ⟨x1, x2, x3, x4, x5⟩, -⟩ := hpre
  obtain ⟨-, hF, -, LE0, -⟩ := hrt
  simp only [win, K, A, outside_cons, outside_nil, and_true] at x5
  simp only [K, A] at hb'
  simp only [RdIn, win, outside_cons, outside_nil, and_true]
  rw [hm, hsp]
  exact ⟨by omega, by rw [hF.accessible]; exact s.mem.accessible_sub x2 (Or.inl rfl) (Nat.le_refl _) (by omega),
    by omega, LE0.held (x4.sub (Nat.le_refl _) (by omega)), by omega⟩

set_option maxRecDepth 20000 in
/-- the stack object for a callee -/
theorem stkIn_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 240) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ kc) (habove : above ≤ 88) : StkIn R L1 S' stk above st := by
  obtain ⟨⟨-, ⟨-, hb', -, -⟩, -, hout, -, hgrt, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, hstw, hstg, hsta⟩, -⟩ := hpre
  obtain ⟨-, -, -, -, -, hstk0, -, arr0⟩ := hrt
  simp only [K, A] at hout hb'
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw hsta
  simp only [StkIn]
  rw [hm, h28]
  refine ⟨hstk0, by simp only [win, hsp, outside_cons, outside_nil, and_true]; omega, hstg, fun hc => ?_⟩
  rcases arr0 with ⟨e0, e2⟩ | ⟨hIn, -⟩
  · rw [e2] at hc; rw [e0, e2]
    obtain ⟨a1, a2⟩ := hsta hc
    exact ⟨by simp only [win, hsp, outside_cons, outside_nil, and_true]; omega, a2⟩
  · have h1 := fresh_out hIn hout
    unfold Apart at h1
    exact ⟨by simp only [win, hsp, outside_cons, outside_nil, and_true]; omega, fresh_out hIn hgrt⟩

/-- `StkApart` of a range held at entry, at a memory with the runtime facts -/
theorem stkApart_rt {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    {a k : Nat} (h : StkApart s.mem st a k) (hh : Held R L a k) : StkApart M st a k := by
  intro hk
  obtain ⟨h1, h2⟩ := h hk
  obtain ⟨-, -, -, -, -, -, hlen, hor⟩ := hrt
  refine ⟨h1, fun hlt => ?_⟩
  rcases hor with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
  · rw [e2, hlen] at hlt; rw [e0, e2, hlen]; exact h2 hlt
  · have := fresh_apart hIn hAp hh
    unfold Apart at this ⊢
    have : 8 * stLen M st + 8 * (stCap M st - stLen M st) = 8 * stCap M st := by omega
    omega

theorem stkApart_sub {M : Memory} {p c k : Nat} (h : StkApart M st p c) (hk : k ≤ c) : StkApart M st p k := by
  intro hk0
  obtain ⟨h1, h2⟩ := h (by omega)
  exact ⟨by unfold Apart at h1 ⊢; omega, fun hlt => by have := h2 hlt; unfold Apart at this ⊢; omega⟩

end

end FvModexp.Arm64.ModInv
