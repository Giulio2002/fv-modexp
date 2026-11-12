import FvModexp.Proofs.Arm64.Nat.StackNatN
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcLsl

/-!
# window-2 entry (arm64): pcs and the frame facts after the prologue

`nat.expNNOddMontgomeryWindowSize2` (fn = 0x1b7eb0 = 1801904) from its entry to `xnE` (fn+0x1a4): prologue (640-byte
frame, saved FP at `sp - 8`, LR at `sp`), argument spills, the `defer stk.restore(stk.save())` record
(`[552]` = closure 1805072, `[560]` = st, `[568]` = old len, `[624]` = sp + 552) and the INLINE `stk.reserve(11·n)`
(nat.go:333-337 = `slices.Grow` + header update): `growslice`/`memclrNoHeapPointers` when the array is too small, the
header stores with the write barrier, `len := len + rnd(23n)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2En

/-- the function's entry -/
abbrev fnE : Nat := 1801904
/-- the join of `slices.Grow` (fn+0x178, `STP (R14, R15), 8(R3)`) -/
abbrev enJ : Nat := 1802280
/-- return of `growslice` (fn+0xfc) -/
abbrev grRet : Nat := 1802156
/-- return of `memclrNoHeapPointers` (fn+0x12c) -/
abbrev mcRet : Nat := 1802204
/-- return of `gcWriteBarrier2` (fn+0x190) -/
abbrev wbRet : Nat := 1802304
/-- after the inline `stk.reserve` (fn+0x1a4) = `W2Pro.xnE` -/
abbrev xnE : Nat := 1802324
/-- `runtime.growslice` / `memclrNoHeapPointers` / `gcWriteBarrier2` (contract addresses of the extraction) -/
abbrev grE : Nat := 587552
abbrev mcE : Nat := 608976
abbrev wbE : Nat := 608160
/-- the `big.Word` type descriptor -/
abbrev wTy : Nat := 2641088

theorem grE_eq : Extracted.program.contractAddr "runtime.growslice" = grE := by decide
theorem mcE_eq : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = mcE := by decide
theorem wbE_eq : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbE := by decide

/-- the frame slots after the prologue (saved FP/LR, defer record, argument spills) -/
@[reducible] def ESl (M : Memory) (sp st : Nat) (r29 : BitVec 64) (ret zp zc xp xl xc yp ylen mp n mc len0 : Nat) : Prop :=
  M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ M.readLE (sp + 624) 8 = sp + 552 ∧
  M.readLE (sp + 552) 8 = 1805072 ∧ M.readLE (sp + 560) 8 = st ∧ M.readLE (sp + 568) 8 = len0 ∧
  M.readLE (sp + 648) 8 = zp ∧ M.readLE (sp + 664) 8 = zc ∧ M.readLE (sp + 672) 8 = st ∧
  M.readLE (sp + 680) 8 = xp ∧ M.readLE (sp + 688) 8 = xl ∧ M.readLE (sp + 696) 8 = xc ∧
  M.readLE (sp + 704) 8 = yp ∧ M.readLE (sp + 712) 8 = ylen ∧ M.readLE (sp + 728) 8 = mp ∧
  M.readLE (sp + 736) 8 = n ∧ M.readLE (sp + 744) 8 = mc

theorem rnd11 (n : Nat) (hn : n ≤ 128) :
    (BitVec.ofNat 64 (11 * n) + 3#64) &&& BitVec.ofNat 64 18446744073709551612 =
      BitVec.ofNat 64 (StackNat.rnd (11 * n)) := by
  have := StackNat.rnd_bv (BitVec.ofNat 64 (11 * n)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 11 * n < 2 ^ 64 by omega)]; omega)
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 11 * n < 2 ^ 64 by omega)] at this

theorem mul11 (n : Nat) (hn : n ≤ 128) : BitVec.ofNat 64 n * 11#64 = BitVec.ofNat 64 (11 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]; omega

theorem mul11' (n : Nat) (hn : n ≤ 128) : 11#64 * BitVec.ofNat 64 n = BitVec.ofNat 64 (11 * n) := by
  rw [BitVec.mul_comm]; exact mul11 n hn

end FvModexp.Arm64.W2En
