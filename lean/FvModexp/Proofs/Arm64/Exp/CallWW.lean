import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.CallW

/-!
# `CallW.hypSum` for `LibW.program` (arm64; agent infra)

`LibW` = `LibExp` without `nat.expNNOdd`, `nat.expNN`, `nat.expNNEven`, `(*Int).exp`: the program of the power-of-two
layer (`buildPrecomputationWindowModPower2`, `expNNPowerOfTwoWindowSize2/4`, `expNNPowerOfTwo`), so its summaries can be
called (as `Ensures` on `LibW.names`) from `nat.expNN`'s program `LibN` (NESTED-PROGRAM RULE). Light copy of
`LibWC.hypSum` (that module imports the montgomery layer).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.CallWW

theorem hypSum {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {f : String} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibW.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibW.eq_only] at hS
  exact hS

end FvModexp.Arm64.CallWW
