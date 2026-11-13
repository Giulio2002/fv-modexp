import FvModexp.Proofs.Amd64.NatQ.DivMFull
import FvModexp.Proofs.Amd64.NatQ.DivCG
import FvModexp.Proofs.Amd64.Int.LibMod

set_option autoImplicit false

/-! (amd64 twin (top s46) of Arm64/NatQ/DivMC.lean, TIGHT COSTS)
# `nil.div(nil, u, u, v)` (amd64, `stk == nil`, `z2 = u`) CLOSED: `IMod.DivHypM` with every callee discharged

`ensMC` = `ensML` with the Q `DivLarge.ensG` (`divRecursiveStep` = asm's amd64 `Q.DivRec.hyp`, `nat.mul` = divmc's amd64
`Q.NatMul.hypQE`); cost instance `Q.NatDiv.costMQ Q.drsCQ`. Remaining hypotheses: only the live runtime contracts on
`Extracted.program.ofImpl impl`. Also the program facts divmc's `IMod` composition asks for (`hnsD`, `hnsQ`) for
`nsD = LibDiv.names`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv

/-- **`nat.div`** (amd64) as `(*Int).Mod` → `(*Int).QuoRem` calls it, every callee discharged -/
theorem ensMC (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput0 : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh) :
    IMod.DivHypM impl R LibDiv.names 41512 112 (costMQ drsCQ) :=
  ensML impl hap R hmk0 hmv0 hmz0 hno0 hget0 hput0 drsCQ
    (DivLarge.ensG impl hap R hgr hmc hwb hmk0 hmv0 drsCQ
      (Q.DivRec.hyp impl hap R Q.NatMul.names mul_ns (mul_code impl hap)
        (Q.NatMul.hypQE impl hap R hmk0 hgr hmc hmv0 hwb mulWX64) hgr hmc hwb hmv0))

/-- divmc's `hnsD` for `nsD = LibDiv.names` -/
theorem libDiv_sub_mod : ∀ x, LibDiv.names.contains x = true → LibMod.names.contains x = true := by
  have h : LibDiv.names.all (fun x => LibMod.names.contains x) = true := by decide
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (List.contains_iff_mem.1 hx)

/-- divmc's `hnsQ` for `nsD = LibDiv.names` -/
theorem libDiv_noQuoRem : LibDiv.names.contains Extracted.seg6.name = false := by decide

end FvModexp.Amd64.Q.NatDiv
