import FvModexp.Proofs.Arm64.NatQ.DivMFull
import FvModexp.Proofs.Arm64.NatQ.DivCG

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivMC.lean, TIGHT COSTS, asm s38)
# `nil.div(nil, u, u, v)` (arm64, `stk == nil`, `z2 = u`) CLOSED: `IMod.DivHypM` with every callee discharged

`ensMC` = `ensML` with the Q `DivLarge.ens` (`divRecursiveStep` = `Q.DivRec.hyp`, `nat.mul` = `Q.DivRec.mulHyp`, divmc's `Q.NatMul.ens`);
cost instance `Q.NatDiv.costMQ Q.drsCQ` (the plain form: the stack is owned, its reserve `stkRes (16·len u + 64)` paid once).
Remaining hypotheses: only the live runtime contracts on `Extracted.program.ofImpl impl`. Also the program facts
divmc's `IMod.ens` asks for (`hnsD`, `hnsQ`) for `nsD = LibDiv.names`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
open Janus.Contracts.Pool FvModexp

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

/-- **`nat.div`** (arm64) as `(*Int).Mod` → `(*Int).QuoRem` calls it, every callee discharged -/
theorem ensMC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno0 : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh) :
    IMod.DivHypM impl R LibDiv.names 41504 112 (costMQ drsCQ) :=
  ensML impl hap R hmk0 hmv0 hmz0 hno0 hget0 hput0 drsCQ
    (DivLarge.ens impl hap R hgr hmc hwb hmk0 hmv0 drsCQ
      (Q.DivRec.hyp impl hap R NatMul.names mul_ns (mul_code impl hap)
        (Q.DivRec.mulHyp impl hap R hmk0 hgr hmc hmv0 hwb) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmv0))

/-- divmc's `hnsD` for `nsD = LibDiv.names` -/
theorem libDiv_sub_mod : ∀ x, LibDiv.names.contains x = true → LibMod.names.contains x = true := by
  have h : LibDiv.names.all (fun x => LibMod.names.contains x) = true := by decide
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (List.contains_iff_mem.1 hx)

/-- divmc's `hnsQ` for `nsD = LibDiv.names` -/
theorem libDiv_noQuoRem : LibDiv.names.contains Extracted.seg6.name = false := by decide

end FvModexp.Arm64.Q.NatDiv
