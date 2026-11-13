import FvModexp.Proofs.Amd64.NatQ.DrsB1
import FvModexp.Proofs.Amd64.NatQ.DrsB2
import FvModexp.Proofs.Amd64.NatQ.DrsB3N
import FvModexp.Proofs.Amd64.NatQ.DrsB3C
import FvModexp.Proofs.Amd64.NatQ.DrsB4
import FvModexp.Proofs.Amd64.NatQ.DrsCL
import FvModexp.Proofs.Amd64.NatQ.DrsDL

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsLoop.lean)
# `divRecursiveStep` (amd64): the wide-digit loop `for j > B { … ; j -= B }` (natdiv.go:793-854)

* `body`: one iteration, `H j` (`B < j`) → `H (j - B)`: `b1` (head, `clear(qhat)`), `b2` (the recursive call, via the
  induction hypothesis `IH` on `len v`), `b3n`/`b3s` (`qhat.norm()`, `stk.nat(3n)`, `clear(qhatv)`), `b4` (`nat.mul`),
  `cl` (the correction loop), `after` (`cmp`/`subVV`/`subVW`/`addTo`, `stk.restore`).
* `loop`: from any `H j` to an `H j'` with `j' ≤ B` (the loop exit `JLE` → the final block `0x5f00d0`), by induction.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

/-- **one iteration of the wide-digit loop** -/
theorem body (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (ih : ∀ a, IH impl R c.vl a) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (hH : H R c s Lk bk S j) (hj : c.vl / 2 < j) (Q : State → Prop)
    (k : ∀ (L' : List (Nat × Nat)) (b' : Nat) (S' : State), H R c s L' b' S' (j - c.vl / 2) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q :=
  b1 impl R hmc' c s Lk bk S j hH hj Q fun S1 hA1 =>
    b2 impl R c ih s Lk bk S1 j _ _ hA1 Q fun L2 b2' S2 hA2 =>
      b3n impl R c s L2 b2' S2 j _ _ hA2 Q fun X3 qn hN3 =>
        b3s impl hap R hgr hmc hwb hmc' c s L2 b2' X3 j _ _ qn hN3 Q fun L3 b3' S3 hA3 =>
          b4 impl hap R ns hns hcode hmul c s L3 b3' S3 j _ _ qn hA3 Q fun L4 b4' S4 hC =>
            cl impl hap R hmv c s j _ _ _ Q 2 L4 b4' S4 0 _ rfl hC fun L5 b5 S5 hE =>
              after impl hap R hmv c s L5 b5 S5 j _ _ _ hE Q k

/-- **the wide-digit loop**: from the head at `j` to the head at some `j' ≤ B` -/
theorem loop (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (ih : ∀ a, IH impl R c.vl a) (s : State) (Q : State → Prop)
    (kF : ∀ (L' : List (Nat × Nat)) (b' : Nat) (S' : State) (j' : Nat), j' ≤ c.vl / 2 → H R c s L' b' S' j' →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ∀ (n j : Nat) (Lk : List (Nat × Nat)) (bk : Nat) (S : State), j ≤ n → H R c s Lk bk S j →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  intro n
  induction n with
  | zero => intro j Lk bk S hj hH; exact kF Lk bk S j (by omega) hH
  | succ n ihn =>
    intro j Lk bk S hj hH
    by_cases hB : c.vl / 2 < j
    · have h40 := hH.cr.h40
      exact body impl hap R ns hns hcode hmul hgr hmc hwb hmc' hmv c ih s Lk bk S j hH hB Q
        fun L' b' S' hH' => ihn (j - c.vl / 2) L' b' S' (by omega) hH'
    · exact kF Lk bk S j (by omega) hH

end FvModexp.Amd64.Q.DivRec
