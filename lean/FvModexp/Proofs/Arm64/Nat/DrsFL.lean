import FvModexp.Proofs.Arm64.Nat.DrsF1
import FvModexp.Proofs.Arm64.Nat.DrsF2
import FvModexp.Proofs.Arm64.Nat.DrsF3
import FvModexp.Proofs.Arm64.Nat.DrsF4
import FvModexp.Proofs.Arm64.Nat.DrsFCL
import FvModexp.Proofs.Arm64.Nat.DrsFDL

/-!
# `divRecursiveStep` (arm64): the final block (natdiv.go:856-892), composed

`final`: from the loop head `H j` with `j ≤ B` (the `BLE` to `0x1ba92c`) to the return with `Kept ∧ DrsPostW`:
`f1` (`clear(qhat)`), `f2` (the recursive call on `u[s:].norm()`, `v[s:]`, via `IH`), `f3n`/`f3s` (`qhat.norm()`,
`stk.nat(3n)`, `clear(qhatv)`), `f4` (`nat.mul`), `clF` (the correction loop), `afterF` (the rest and the return).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- **the final block** -/
theorem final (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypXE impl R ns stkM aboveM mulC) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (ih : ∀ a, IH impl R c.vl a) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (hj : j ≤ c.vl / 2) (hH : H R c s Lk bk S j) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S (QF R c s) :=
  f1 impl R hmc' c s Lk bk S j hH hj _ fun S1 hA1 =>
    f2 impl R c ih s Lk bk S1 j _ _ hA1 _ fun L2 b2' S2 hA2 =>
      f3n impl R c s L2 b2' S2 j _ _ hA2 _ fun X3 qn hN3 =>
        f3s impl hap R hgr hmc hwb hmc' c s L2 b2' X3 j _ _ qn hN3 _ fun L3 b3' S3 hA3 =>
          f4 impl hap R ns hns hcode hmul hk ha c s L3 b3' S3 j _ _ qn hA3 _ fun L4 b4' S4 hC =>
            clF impl hap R hmv c s j _ _ _ _ 2 L4 b4' S4 0 _ rfl hC fun L5 b5 S5 hE =>
              afterF impl hap R hmv c s L5 b5 S5 j _ _ _ hE

end FvModexp.Arm64.DivRec
