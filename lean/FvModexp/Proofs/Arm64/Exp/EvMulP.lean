import FvModexp.Proofs.Arm64.Exp.EvDst
import FvModexp.Proofs.Arm64.Nat.SqrMulXR

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `nat.mul`'s precondition (`MulHypG` form) at `z.mul(stk, x, y)` (agent infra)

`mulPreG`: `MulPreG ∧ CapIn0 x ∧ CapIn0 y ∧ MulXG` at the callee entry (`SP = sp`) for a destination `z` (located, or
EMPTY with `EL`), an operand `x` that may be empty, an operand `y`; both operands live locals.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

theorem mul_a : segAddr Extracted.program fnMul = 1814128 := by decide

/-- a value below `2^n` (`n < 64 ml`) has at most `ml` limbs -/
theorem len_ml {M : Memory} {p l v n : Nat} (hN : NatNorm M p l) (hv : natVal M p l = v) (hlt : v < 2 ^ n)
    {ml : Nat} (hn : n < 64 * ml) : l ≤ ml :=
  nlen_bd' hN (by rw [hv]; exact Nat.lt_trans hlt (Nat.pow_lt_pow_right (by decide) hn))

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- `miOp` for any prefix length (vacuous when empty) -/
theorem miOp0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p l c v : Nat} (hq : LN R L s.mem st M L1 p l c v)
    {k' : Nat} (hk : k' ≤ 8 * c) : StkApart M st p k' ∧ OpX M st p k' := by
  rcases Nat.eq_zero_or_pos k' with e | e
  · subst e; exact ⟨fun h0 => absurd h0 (Nat.lt_irrefl 0), fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
  · exact miOp hP h hq (by omega) hk

/-- `CapIn0` of a live local -/
theorem LN.capIn0 {m0 : Memory} {p l c v : Nat} (hq : LN R L m0 st M L1 p l c v) : CapIn0 R L1 p l c :=
  ⟨hq.2.1, hq.1.1, fun h0 => ⟨(hq.1.2.1 h0).2.1, (hq.1.2.1 h0).2.2.2⟩⟩

/-- an operand as `RdIn0` -/
theorem LN.rd0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p l c v : Nat}
    (hq : LN R L s.mem st M L1 p l c v) {S : State} (hsp : S.sp.toNat = sp) (hm : S.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 128) : ExpHyp.RdIn0 R L1 S stk above p l :=
  ⟨by have := hq.1.1; have := hq.2.1; omega, fun h0 => LN.rd hP hq (by have := hq.2.1; omega) hsp hm hstk habove⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.mul`'s precondition** (`MulHypG` form) at the callee entry `S'` (`SP = sp`) -/
theorem mulPreG (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88)
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {pd ld cd vd px lx cx vx py ly cy vy : Nat}
    (hd : LN R L s.mem st M L1 pd ld cd vd) (hde : EL R L pd cd)
    (hx : LN R L s.mem st M L1 px lx cx vx) (hy : LN R L s.mem st M L1 py ly cy vy)
    (hdx : 0 < cx → 0 < cd → Apart px (8 * cx) pd (8 * cd)) (hdy : 0 < cy → 0 < cd → Apart py (8 * cy) pd (8 * cd))
    (hlx : lx ≤ 2 ^ 12) (hly : ly ≤ 2 ^ 12) (hs16 : ℓ + 4 * (lx + ly) + 64 ≤ 2 ^ 16) {c : Nat} (hb : c ≤ b1) :
    MulPreG R b1 c L1 stk above pd ld cd st px lx py ly S' ∧ CapIn0 R L1 px lx cx ∧ CapIn0 R L1 py ly cy ∧
      MulXG R L1 S' stk above st pd cd px lx cx py ly cy := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hout := hP.win_rt
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := stk) (above := above) hstk habove
  have hgl := hw.globals hP (w := win S' stk above) (fun a n ho => by
    simp only [win, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hwr := DL.wr hP hd.1 hsN hgN fm (stk := stk) (above := above) hstk (by omega)
  have hrx := LN.rd0 hP hx hsN fm (stk := stk) (above := above) hstk (by omega)
  have hry := LN.rd0 hP hy hsN fm (stk := stk) (above := above) hstk (by omega)
  have hsi := hw.stkIn hP hsN hgN fm (stk := stk) (above := above) hstk habove
  have hsx := ev_stkX hP hw hsN hgN fm (stk := stk) (above := above) hstk habove
  obtain ⟨od1, od2⟩ := miOp0 hP hw hd (Nat.le_refl (8 * cd))
  obtain ⟨ox1, ox2⟩ := miOp0 hP hw hx (Nat.mul_le_mul_left 8 hx.2.1)
  obtain ⟨oy1, oy2⟩ := miOp0 hP hw hy (Nat.mul_le_mul_left 8 hy.2.1)
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hdw : Outside pd (8 * cd) (win S' stk above) := by
    rcases Nat.eq_zero_or_pos cd with c0 | c0
    · subst c0
      have := EL.out hde hout
      simp only [win, hsN, outside_cons, outside_nil, and_true]; unfold Apart at this; omega
    · exact (hwr.2.2 c0).1
  have hax : pd = px ∨ (0 < cd → 0 < lx → Apart pd (8 * cd) px (8 * lx)) :=
    Or.inr fun hc hl => apart_shrink (hdx (by have := hx.2.1; omega) hc).symm (Nat.mul_le_mul_left 8 hx.2.1)
  have hay : pd = py ∨ (0 < cd → 0 < ly → Apart pd (8 * cd) py (8 * ly)) :=
    Or.inr fun hc hl => apart_shrink (hdy (by have := hy.2.1; omega) hc).symm (Nat.mul_le_mul_left 8 hy.2.1)
  have hex : pd = px → 0 < cd → 0 < lx → cd = cx := fun e hc hl => by
    have := hdx (by have := hx.2.1; omega) hc; rw [e] at this; unfold Apart at this; omega
  have hey : pd = py → 0 < cd → 0 < ly → cd = cy := fun e hc hl => by
    have := hdy (by have := hy.2.1; omega) hc; rw [e] at this; unfold Apart at this; omega
  subst fm
  exact ⟨⟨hce, hsv, hgl, hd.2.1, hwr, hrx, hry, hlx, hly, hax, hay, hsi, by rw [hlen]; exact hs16, od1, ox1, oy1, hb,
    by rw [hgN]; exact hw.inv⟩, hx.capIn0, hy.capIn0, ⟨hsx, hdw, hex, hey, od2, ox2, oy2⟩⟩

end

end FvModexp.Arm64.ExpEven
