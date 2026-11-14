import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4Zm

/-!
# window-4 prologue (arm64): `one := make(nat, n); one[0] = 1`, `var powers [16]nat`, call of `stk.nat(17n)`
(nat.go:1405-1412), from `oneJ` (fn+0x524, `CMP $4, R0`, after `RR` is settled) to the entry of `(*stack).nat`.

For `n ≤ 4` the compiler places `one` in the frame (`[sp+336, sp+368)`, zeroed by two `STP`), otherwise
`makeslice(big.Word, n, n)`. The `powers` headers `[sp+432, sp+816)` are zeroed by a 6-trip `STP.P` loop.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- `CMP $4, R0` (both `RR` paths join here) -/
abbrev oneJ : Nat := 1799828
/-- entry of `(*stack).nat` -/
abbrev snE : Nat := 1784176

/-- the ranges `oneJ → snE` writes besides `R.rt` (makeslice window, `one` frame buffer, `powers`, `&one`) -/
@[reducible] def ow (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 336, sp + 368), (sp + 432, sp + 824)]

/-- the facts at the `stk.nat(17n)` call -/
@[reducible] def OnePost (R : RtInv) (L L' : List (Nat × Nat)) (b b' g sp n : Nat) (M M' : Memory) (onep : Nat) :
    Prop :=
  Env R L' g sp M' ∧ LiveExt R L L' ∧ b - (if 4 < n then blockSize (8 * n) true else 0) ≤ b' ∧
  MemFrame M M' (R.rt ++ ow sp) ∧ LiveFrame M M' L [] ∧ R.inv b' L' g (view R.rt L' M') ∧
  M'.regions = M.regions ∧ M'.readLE (sp + 816) 8 = onep ∧ M'.readLE onep (8 * n) = 1 ∧
  ((onep = sp + 336 ∧ n ≤ 4) ∨ (InRanges onep (8 * n) L' ∧ InRanges onep (8 * n) R.rt ∧ ApartAll onep (8 * n) L ∧
    M'.accessible onep (8 * n) true = true ∧ onep + 8 * n ≤ 2 ^ 48 ∧ onep % 8 = 0))

theorem e17 {n : Nat} (hn : n ≤ 2 ^ 16) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 (n * 16) = BitVec.ofNat 64 (17 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `ADD $432, RSP, R2` (the `powers` zeroing loop is next) -/
abbrev zl0 : Nat := 1799920

end FvModexp.Arm64.W4Pro
