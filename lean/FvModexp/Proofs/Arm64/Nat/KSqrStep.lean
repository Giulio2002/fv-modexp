import FvModexp.Proofs.Arm64.Nat.KSqrPro
import FvModexp.Proofs.Arm64.Nat.KSqrSub
import FvModexp.Proofs.Arm64.Nat.KSqrS1
import FvModexp.Proofs.Arm64.Nat.KSqrS2
import FvModexp.Proofs.Arm64.Nat.KSqrS3
import FvModexp.Proofs.Arm64.Nat.KSqrAdd1
import FvModexp.Proofs.Arm64.Nat.KSqrAdd2
import FvModexp.Proofs.Arm64.Nat.KSqrEnd

/-!
# `karatsubaSqr` (arm64): the member step of the squaring SCC

`ksqr_step`: from the induction hypothesis below the measure `2·n`, the summary of `karatsubaSqr` (member `(true, a)`):
`kPro` → `kSub` → `kS1` → `kS2` → `kS3` → `kA1` → `kA2` → `kEnd` (the three inner `nat.sqr` calls use the hypothesis).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ksqr_step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (m : Nat) (ih : ∀ j, IH impl R m j) (a : Args) :
    Summary (LibSqr.program.link impl) (entryOf (true, a)) (fun s => preOf R (true, a) s ∧ μ (true, a) s = m)
      (postOf R (true, a)) := by
  intro s hpc ⟨⟨⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6⟩, hpre⟩, hμ⟩
  have hμ' : 2 * a.a5.toNat = m := hμ
  subst hμ'
  have hzl : a.a2.toNat = 2 * a.a5.toNat := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hzl] at hpre
  show ReachesRet _ (s.regs 30) s fun s' => Kept s s' ∧ KPost R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat
    a.a4.toNat a.a5.toNat s s'
  rw [hzl]
  have ih' : ∀ a', IH impl R (2 * a.a5.toNat) (false, a') := fun a' => ih (false, a')
  refine kPro impl hap R hgr hmc hwb hpre hpc (by rw [h0, bv_ofNat_toNat]) (by rw [h1, bv_ofNat_toNat])
    (by rw [h2, ← hzl, bv_ofNat_toNat]) (by rw [h3, bv_ofNat_toNat]) (by rw [h4, bv_ofNat_toNat])
    (by rw [h5, bv_ofNat_toNat]) (by rw [h6, bv_ofNat_toNat]) ?_
  intro S1 lx0 lx1 Lk1 bk1 hB1
  refine kSub impl hap R hmk hmv hwb S1 hB1 fun S2 Lk2 bk2 tng ltx hB2 => ?_
  refine kS1 impl hap R hmc ih' S2 hB2 fun S3 Lk3 bk3 l1 hB3 => ?_
  refine kS2 impl R ih' S3 hB3 fun S4 Lk4 bk4 l1' l0 hB4 => ?_
  refine kS3 impl R ih' S4 hB4 fun S5 Lk5 bk5 l1'' l0' l2 hB5 => ?_
  refine kA1 impl hap R hmk hmv hwb S5 hB5 fun S6 Lk6 bk6 ng l l2' hB6 => ?_
  refine kA2 impl hap R hmk hmv hwb S6 hB6 fun S7 Lk7 bk7 l' hB7 => ?_
  exact kEnd impl hap R hmv S7 hB7 hl4 hl48

end FvModexp.Arm64.NatSqr
