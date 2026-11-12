import FvModexp.Proofs.Arm64.Nat.NatAddDefs

set_option autoImplicit false

/-!
# `nat.add` (arm64) with empty-tolerant operands: statement pieces (coordinator decision on "[infra s30] FINDING")

As `NatSub0Defs`: a zero-length operand carries no location fact, an empty `z` no window fact. Go's `nat.add` never
dereferences such an operand (`m < n` swaps, `m == 0` returns `z[:0]`, `n == 0` returns `z.set(x)`). infra's use `z.add(z, t)` (expNNEven, nat.go:844) can pass an empty `z` AND an empty `t`, so BOTH operands
are empty-tolerant here.

* `Pre0` = the compact form (operand facts grouped under `0 < len`);
* `PreS0` = `PreS` weakened IN PLACE (same 25 conjuncts, same positions).

`z`'s window fact `Outside zp (8 zc) (win …)` stays UNGUARDED (as in infra's `SubMod2N.PreG`): for `cap z = 0` it says
that `z`'s pointer is not strictly inside the window (true for `nil` and every runtime pointer); the self-call's frame
argument needs it (the callee's write set `[(zp, zp + 8 min(…, zc))]` must miss the caller's LR/FP slots).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatAdd

/-- `PreS` with empty-tolerant operands, weakened in place (25 conjuncts as `PreS`). -/
def PreS0 (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64)
    (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧ xc.toNat < 2 ^ 40 ∧
    yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s stk 80) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (0 < yl.toNat → zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true) ∧
    (0 < xl.toNat → xp.toNat + 8 * xl.toNat ≤ 2 ^ 48) ∧
    (0 < xl.toNat → Held R L xp.toNat (8 * xl.toNat)) ∧ NatNorm s.mem xp.toNat xl.toNat ∧
    NatNorm s.mem yp.toNat yl.toNat ∧ (0 < xl.toNat → Outside xp.toNat (8 * xl.toNat) (win s stk 80)) ∧
    (0 < yl.toNat → s.mem.accessible yp.toNat (8 * yl.toNat) false = true) ∧
    (0 < yl.toNat → yp.toNat + 8 * yl.toNat ≤ 2 ^ 48) ∧
    (0 < yl.toNat → Held R L yp.toNat (8 * yl.toNat)) ∧ (0 < yl.toNat → Outside yp.toNat (8 * yl.toNat) (win s stk 80)) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl yl → R.ok (cA "runtime.makeslice") [wordT, need xl yl, makeCap (need xl yl)] ∧
      makeCost (need xl yl) ≤ b) ∧
    (∀ d src k, k ≤ 8 * mx xl yl → R.ok (cA "runtime.memmove") [d, src, k])

/-- **The empty-tolerant precondition** of `nat.add` (stack `4464`, as `Pre`). -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4464 80 ∧ Outside wordT 16 R.rt ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧ xc.toNat < 2 ^ 40 ∧
    yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s 4464 80) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (0 < yl.toNat → zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4464 80)) ∧
    NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧
    (0 < yl.toNat → s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
      Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s 4464 80)) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl yl → R.ok (cA "runtime.makeslice") [wordT, need xl yl, makeCap (need xl yl)] ∧
      makeCost (need xl yl) ≤ b) ∧
    (∀ d src k, k ≤ 8 * mx xl yl → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre0.toS0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : Pre0 R b L zp zc xp xl xc yp yl yc s) : PreS0 4464 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun h => (a13 h).1, fun h => (a13 h).2.1,
    fun h => (a13 h).2.2.1, a14, a15, fun h => (a13 h).2.2.2, fun h => (a16 h).1, fun h => (a16 h).2.1,
    fun h => (a16 h).2.2.1, fun h => (a16 h).2.2.2, a17, a18, a19⟩

/-- the old precondition gives the empty-tolerant one -/
theorem Pre.to0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : Pre R b L zp zc xp xl xc yp yl yc s) : Pre0 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    fun hz => ⟨(a12 hz).1, fun _ => (a12 hz).2.1, fun _ => (a12 hz).2.2⟩, fun _ => ⟨a13, a14, a15, a18⟩, a16, a17,
    fun _ => ⟨a19, a20, a21, a22⟩, a23, a24, a25⟩

/-- with non-empty `z`, `x`, `y` the empty-tolerant precondition is the old one -/
theorem PreS0.toS {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} (h : PreS0 stk R b L zp zc xp xl xc yp yl yc s) (hx : 0 < xl.toNat)
    (hy : 0 < yl.toNat) : PreS stk R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    fun hz' => ⟨(a12 hz').1, (a12 hz').2.1 hx, (a12 hz').2.2 hy⟩, a13 hx, a14 hx, a15 hx, a16, a17, a18 hx, a19 hy,
    a20 hy, a21 hy, a22 hy, a23, a24, a25⟩

theorem preS0_mono {stk stk' : Nat} (hk : stk' ≤ stk) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl xc yp yl yc : BitVec 64} {s : State} (h : PreS0 stk R b L zp zc xp xl xc yp yl yc s) :
    PreS0 stk' R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨hce, h1, h2, h3, h4, h5, h6, h7, h8, h9, hzo, hzw, h10, h11, h12, h13, h14, hxw, h15, h16, h17, hyw, h18⟩ := h
  have hsp := hce.2.1.2.1
  refine ⟨callEnv_mono hk hce, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, hzw, h10, h11, h12, h13, h14,
    fun hc => ?_, h15, h16, h17, fun hc => ?_, h18⟩
  · simp only [win, outside_cons, outside_nil, and_true] at hzo ⊢; omega
  · have := hxw hc; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  · have := hyw hc; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega

end FvModexp.Arm64.NatAdd
