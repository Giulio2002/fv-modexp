import FvModexp.Proofs.Arm64.NatQ.SqrStep
import FvModexp.Proofs.Arm64.NatQ.KSqrStep

/-!
# [Q-form copy of Arm64/Nat/SqrSCC.lean — TIGHT COSTS, divmc s34] The squaring SCC `{nat.sqr, karatsubaSqr}` (arm64): both summaries by `Summary.induction_mutual`

`scc`: every member's summary on `LibSqr.program`, from `sqr_step` (`nat.sqr`, measure `2·len x + 1`) and `ksqr_step`
(`karatsubaSqr`, measure `2·len x`); premises are the live runtime contracts only.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

theorem scc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ∀ j : Mem, Summary (LibSqr.program.link impl) (entryOf j) (preOf R H j) (postOf R H j) :=
  Summary.induction_mutual μ fun m ih j => by
    rcases j with ⟨k, a⟩
    cases k
    · exact sqr_step impl hap R hmk hgr hmc hwb m ih a
    · exact ksqr_step impl hap R hmk hgr hmc hmv hwb m ih a

end FvModexp.Arm64.Q.NatSqr
