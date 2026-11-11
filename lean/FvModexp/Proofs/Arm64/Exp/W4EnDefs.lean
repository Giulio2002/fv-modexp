import FvModexp.Proofs.Arm64.Exp.W4Defs
import FvModexp.Proofs.Arm64.Nat.StackNatN
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcLsl

/-!
# window-4 entry (arm64): pcs and the frame facts after the prologue

`nat.expNNOddMontgomeryWindowSize4` (fn = 0x1b7170 = 1798512) from its entry to `xnE` (fn+0x1a4): prologue (928-byte
frame, saved FP at `sp - 8`, LR at `sp`), argument spills, the `defer stk.restore(stk.save())` record
(`[840]` = closure 1801824, `[848]` = st, `[856]` = old len, `[912]` = sp + 840) and the INLINE `stk.reserve(23·n)`
(nat.go:333-337 = `slices.Grow` + header update): `growslice`/`memclrNoHeapPointers` when the array is too small, the
header stores with the write barrier, `len := len + rnd(23n)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

/-- the function's entry -/
abbrev fnE : Nat := 1798512
/-- the join of `slices.Grow` (fn+0x178, `STP (R14, R15), 8(R3)`) -/
abbrev enJ : Nat := 1798888
/-- return of `growslice` (fn+0xfc) -/
abbrev grRet : Nat := 1798764
/-- return of `memclrNoHeapPointers` (fn+0x12c) -/
abbrev mcRet : Nat := 1798812
/-- return of `gcWriteBarrier2` (fn+0x190) -/
abbrev wbRet : Nat := 1798912
/-- after the inline `stk.reserve` (fn+0x1a4) = `W4Pro.xnE` -/
abbrev xnE : Nat := 1798932
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
  M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ M.readLE (sp + 912) 8 = sp + 840 ∧
  M.readLE (sp + 840) 8 = 1801824 ∧ M.readLE (sp + 848) 8 = st ∧ M.readLE (sp + 856) 8 = len0 ∧
  M.readLE (sp + 936) 8 = zp ∧ M.readLE (sp + 952) 8 = zc ∧ M.readLE (sp + 960) 8 = st ∧
  M.readLE (sp + 968) 8 = xp ∧ M.readLE (sp + 976) 8 = xl ∧ M.readLE (sp + 984) 8 = xc ∧
  M.readLE (sp + 992) 8 = yp ∧ M.readLE (sp + 1000) 8 = ylen ∧ M.readLE (sp + 1016) 8 = mp ∧
  M.readLE (sp + 1024) 8 = n ∧ M.readLE (sp + 1032) 8 = mc

theorem rnd23 (n : Nat) (hn : n ≤ 128) :
    (BitVec.ofNat 64 (23 * n) + 3#64) &&& BitVec.ofNat 64 18446744073709551612 =
      BitVec.ofNat 64 (StackNat.rnd (23 * n)) := by
  have := StackNat.rnd_bv (BitVec.ofNat 64 (23 * n)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 23 * n < 2 ^ 64 by omega)]; omega)
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 23 * n < 2 ^ 64 by omega)] at this

theorem mul23 (n : Nat) (hn : n ≤ 128) : BitVec.ofNat 64 n * 23#64 = BitVec.ofNat 64 (23 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]; omega

theorem mul23' (n : Nat) (hn : n ≤ 128) : 23#64 * BitVec.ofNat 64 n = BitVec.ofNat 64 (23 * n) := by
  rw [BitVec.mul_comm]; exact mul23 n hn

end FvModexp.Arm64.W4En
