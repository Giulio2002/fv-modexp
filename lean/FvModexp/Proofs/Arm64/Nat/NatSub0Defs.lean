import FvModexp.Proofs.Arm64.Nat.NatSubDefs

set_option autoImplicit false

/-!
# `nat.sub` (arm64) with empty-tolerant operands: statement pieces (coordinator decision on "[infra s30] FINDING")

A zero-length operand (e.g. a `nil` nat returned by `nat.expNN`) carries no location fact, and an empty `z`
(`cap z = 0`) no window fact. Go's `nat.sub` never dereferences such an operand: `m == 0` returns `z[:0]`, `n == 0`
returns `z.set(x)`, `cap z = 0 < m` allocates.

* `Pre0` = infra's `SubMod2N.SubPre0` (same body, so `SubHypR0` is `ensR0` by definitional unfolding);
* `PreS0` = `PreS` weakened IN PLACE (same 27 conjuncts, same positions, so the path proofs destructure it alike):
  slot 13 (`z` outside the window) guarded by `0 < zc`, the operand facts of `x` / `y` by `0 < len`, the aliasing
  facts inside slot 14 by `0 < len`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatSub

/-- `PreS` with empty-tolerant operands, weakened in place (27 conjuncts as `PreS`). -/
def PreS0 (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64)
    (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧
    xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s stk 80)) ∧
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
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

/-- **The empty-tolerant precondition** (body = infra's `SubMod2N.SubPre0`). -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4304 80 ∧ Outside wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧
    xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4304 80)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (0 < yl.toNat → zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4304 80)) ∧
    NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧
    (0 < yl.toNat → s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
      Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s 4304 80)) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre0.toS0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : Pre0 R b L zp zc xp xl xc yp yl yc s) : PreS0 4304 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, fun h => (a15 h).1, fun h => (a15 h).2.1,
    fun h => (a15 h).2.2.1, a16, a17, fun h => (a15 h).2.2.2, fun h => (a18 h).1, fun h => (a18 h).2.1,
    fun h => (a18 h).2.2.1, fun h => (a18 h).2.2.2, a19, a20, a21⟩

/-- the old precondition gives the empty-tolerant one -/
theorem Pre.to0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : Pre R b L zp zc xp xl xc yp yl yc s) : Pre0 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun _ => a13,
    fun hz => ⟨(a14 hz).1, fun _ => (a14 hz).2.1, fun _ => (a14 hz).2.2⟩, fun _ => ⟨a15, a16, a17, a20⟩, a18, a19,
    fun _ => ⟨a21, a22, a23, a24⟩, a25, a26, a27⟩

/-- with non-empty `z`, `x`, `y` the empty-tolerant precondition is the old one -/
theorem PreS0.toS {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} (h : PreS0 stk R b L zp zc xp xl xc yp yl yc s) (hz : 0 < zc.toNat) (hx : 0 < xl.toNat)
    (hy : 0 < yl.toNat) : PreS stk R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 hz,
    fun hz' => ⟨(a14 hz').1, (a14 hz').2.1 hx, (a14 hz').2.2 hy⟩, a15 hx, a16 hx, a17 hx, a18, a19, a20 hx, a21 hy,
    a22 hy, a23 hy, a24 hy, a25, a26, a27⟩

end FvModexp.Arm64.NatSub
