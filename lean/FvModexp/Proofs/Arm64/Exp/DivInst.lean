import FvModexp.Proofs.Arm64.Nat.Div
import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Arm64.Exp.LibW

/-!
# `nat.div` (arm64) as the windows' premise `ExpHyp.DivHyp`

asm's `NatDiv.ens` / `ensD` (Arm64/Nat/Div.lean) carry `DivPre ∧ HdrSep`; `HdrSep` is a conjunct of `DivPre` (asm s18,
expmc s24), so they give `ExpHyp.DivHyp … LibDiv.names 41504 112 (NatDiv.cost dc)` exactly. Plus the name facts the
windows' / `expNNOdd`'s / `expNN`'s statements ask of `nsD`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.DivInst

set_option maxRecDepth 20000 in
theorem hdr {R : RtInv} {b : Nat} {cost : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {stk above zp zl zc st z2 z2l z2c u ul v vl : Nat} {s : State}
    (h : ExpHyp.DivPre R b cost L stk above zp zl zc st z2 z2l z2c u ul v vl s) : NatDiv.HdrSep s st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
  exact hh

/-- `nat.div` with `divLarge` as a premise -/
theorem hyp (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc) :
    ExpHyp.DivHyp impl R LibDiv.names 41504 112 (NatDiv.cost dc) := by
  intro b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs hpre
  exact NatDiv.ens impl hap R hmk0 hmv0 hmz0 dc hL b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs
    hpre

/-- `nat.div` with `divLarge` discharged: premise `DrsHyp` (`divRecursiveStep`) -/
theorem hypD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (dc : Nat → Nat → Nat → Nat) (hD : DivLarge.DrsHyp impl R dc) :
    ExpHyp.DivHyp impl R LibDiv.names 41504 112 (NatDiv.cost dc) := by
  intro b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs hpre
  exact NatDiv.ensD impl hap R hgr hmc hwb hmk0 hmv0 hmz0 dc hD b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs
    hpre

set_option maxHeartbeats 64000000 in
theorem ns_sub : ∀ x, LibDiv.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)

theorem ns_w4 : LibDiv.names.contains Extracted.seg34.name = false := by decide

theorem ns_w2 : LibDiv.names.contains Extracted.seg35.name = false := by decide

end FvModexp.Arm64.DivInst
