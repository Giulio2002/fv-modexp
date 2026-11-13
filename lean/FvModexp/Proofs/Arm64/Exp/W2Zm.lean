import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Conv
import FvModexp.Proofs.Arm64.Exp.W2P01Defs
import FvModexp.Proofs.Arm64.Exp.W2ZcDefs

/-!
# window-2 prologue (arm64): `z = z.make(2 * numWords)` (nat.go:1425, nat.go:58-69), `j4 → zj`

Reuse when `2n ≤ cap z`, else `makeslice(Word, 2n, 2n+4)`. Result in X0 (pointer), X14 (capacity), X13 = n at `zj`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

/-- `type:big.Word` -/
@[reducible] def wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- the facts about `z` after `z.make(2n)` -/
@[reducible] def ZPost (R : RtInv) (L L' : List (Nat × Nat)) (b b' g sp n : Nat) (M M' : Memory)
    (zp zc zp' zc' : Nat) : Prop :=
  Env R L' g sp M' ∧ Buf R L' g sp n M' zp' zc' ∧ zp' % 8 = 0 ∧ LiveExt R L L' ∧
  b - blockSize (8 * (2 * n + 4)) true ≤ b' ∧
  MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 152)]) ∧ LiveFrame M M' L [] ∧
  R.inv b' L' g (view R.rt L' M') ∧ M'.regions = M.regions ∧
  ((zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L))

theorem out_inR {a n p k : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hin : InRanges p k rs) :
    a + n ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem h hr
  omega

end FvModexp.Arm64.W2Pro
