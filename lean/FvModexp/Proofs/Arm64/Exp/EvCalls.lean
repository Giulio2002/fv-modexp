import FvModexp.Proofs.Arm64.Exp.LibNE
import FvModexp.Proofs.Arm64.Exp.CallW
import FvModexp.Proofs.Arm64.Exp.LibCalls

set_option autoImplicit false

/-!
# Call helpers on `LibNE.program` (arm64; agent infra) — `CallW.hypSum` / `LibCalls.stkNatCallL` for `LibNE`

`LibNE` = `LibN` ∪ {`nat.expNNEven`}: the program of `nat.expNNEven`'s summary (NESTED-PROGRAM RULE). `hypSum` lifts
an `Ensures` on `onlySegments ns` (`ns ⊆ LibNE.names`) to a `Summary` on `LibNE.program`; the call helpers are the
continuation-form calls of `nat.expNNEven`'s segments.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.CallNE

theorem hypSum {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) {f : String} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibNE.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibNE.eq_only] at hS
  exact hS

theorem stkNatCallL {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) {stk above : Nat}
    (hsn : StackNat.HypL impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {st n : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (bst : st < 2 ^ 64) (bn : n < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : StackNat.Pre R b L stk above st n S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → StackNat.PostL R b L stk above st n S s' →
      ReachesRet (LibNE.program.link impl) ret s' Q) :
    ReachesRet (LibNE.program.link impl) ret S Q := by
  have hS := hypSum hap hns (hsn b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 n))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, LibCalls.tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, trivial⟩
  · rw [LibCalls.tN bst, LibCalls.tN bn]; exact hpre
  · rw [LibCalls.tN bst, LibCalls.tN bn] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

end FvModexp.Arm64.CallNE
