import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Amd64.Exp.CallW
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Amd64.Nat.Callees2

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): calling a callee summary from the function (asm s57)

`codeIn_NE`: a callee program `(Extracted.program.onlySegments ns).link impl` with `ns ⊆ LibNE.names` runs inside
`LibNE.program.link impl`. `snCallE`: the `(*stack).nat` call (`StackNat.HypL`) from its entry (`RSP` = the caller's
`RSP - 8`, return address `ra` at `[RSP]`) to `ra`, the post as `PostL` with the plain arguments.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.ExpEven

theorem codeIn_NE {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) :
    CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibNE.program.link impl) := by
  rw [LibNE.eq_only]; exact A64.codeIn_restrict_mono64 hap hns

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*stack).nat(n)`** from its entry to the return address `ra` -/
theorem snCallE {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) {stk above : Nat}
    (hSN : StackNat.HypL impl R ns stk above)
    {ret : W64} {Q : State → Prop} {b : Nat} {L : List (Nat × Nat)} {st n ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn))
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra) (hst : st < 2 ^ 64) (hn : n < 2 ^ 64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) (hpre : StackNat.Pre R b L stk above st n S)
    (KB : ∀ (S' : State), S'.rip = BitVec.ofNat 64 ra → S'.regs 4 = S.regs 4 + 8 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.xmm 15 = S.xmm 15 → S'.mem.regions = S.mem.regions →
      StackNat.PostL R b L stk above st n S S' → ReachesRet (LibNE.program.link impl) ret S' Q) :
    ReachesRet (LibNE.program.link impl) ret S Q := by
  have hS := Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1) (A64.noExit_restrict64 hap ns) (codeIn_NE hap hns)
  have tst : (BitVec.ofNat 64 st).toNat = st := by simp only [BitVec.toNat_ofNat]; omega
  have tk : (BitVec.ofNat 64 n).toNat = n := by simp only [BitVec.toNat_ofNat]; omega
  refine ReachesRet.call_regions hS hpc ⟨?ra, hx15, hdf, ?pre⟩ (fun s' hr hq hrg => ?_)
  case ra => rw [hrd]; exact hra
  case pre => rw [h0, h3, tst, tk]; exact hpre
  obtain ⟨⟨e4, e5, e14, e15⟩, hq⟩ := hq
  rw [h0, h3, tst, tk] at hq
  exact KB s' (by rw [hr, retAddrOf_eq, hrd]) e4 e5 e14 e15 hrg hq

end FvModexp.Amd64.ExpEven
