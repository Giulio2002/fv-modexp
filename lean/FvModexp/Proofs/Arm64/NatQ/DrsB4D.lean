import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsMulQ
import FvModexp.Proofs.Arm64.NatQ.DrsSN
import FvModexp.Proofs.Arm64.NatQ.DrsCN

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsB4D.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), loop body segment 4 (shared defs): `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831)

`b4`: from `A3` (`0x1ba684`, after `clear(qhatv)`) → the argument loads → `CALL nat.mul` (`0x1ba6ac`, premise
`MulHypXE` on a library program `ns` inside `LibDrs`) → the stores of the result `qhatv` (`SP'+328/152/168`), `i := 0`
→ the correction loop's head `C` (`0x1ba700`) at the model state `Cx.st0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

set_option linter.defProp false in
/-- `nat.mul`'s premise as a summary in `LibDrs.program.link impl` -/
def mulSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypQE impl R ns stkM aboveM mulCQ)
    (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64) :=
  Ensures.toSummaryIn (hmul H b L z zl zc st x xl xc y yl yc) (noExit_restrict hap ns) hcode

/-- the return address of the product -/
abbrev r4 : Nat := 0x1ba6b0

/-- the three stores of `qhatv`'s slots (`SP'+328/152/168`) read back -/
theorem rd3 (M : Memory) (p a b c : Nat) (hp : 248 ≤ p) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (((M.writeLE (p - 72) 8 a).writeLE (p - 248) 8 b).writeLE (p - 232) 8 c).readLE (p - 72) 8 = a ∧
    (((M.writeLE (p - 72) 8 a).writeLE (p - 248) 8 b).writeLE (p - 232) 8 c).readLE (p - 248) 8 = b ∧
    (((M.writeLE (p - 72) 8 a).writeLE (p - 248) 8 b).writeLE (p - 232) 8 c).readLE (p - 232) 8 = c := by
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt ha]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hb]
  · rw [Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hc]

end FvModexp.Arm64.Q.DivRec
