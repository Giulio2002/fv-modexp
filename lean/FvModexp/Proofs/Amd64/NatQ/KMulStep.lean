import FvModexp.Proofs.Amd64.NatQ.KMulPro
import FvModexp.Proofs.Amd64.NatQ.KMulSub
import FvModexp.Proofs.Amd64.NatQ.KMulS1
import FvModexp.Proofs.Amd64.NatQ.KMulS2
import FvModexp.Proofs.Amd64.NatQ.KMulS3
import FvModexp.Proofs.Amd64.NatQ.KMulAdd1
import FvModexp.Proofs.Amd64.NatQ.KMulAdd2
import FvModexp.Proofs.Amd64.NatQ.KMulEnd

set_option autoImplicit false

/-!
# [amd64 port (divmc s53) of the Q-form Arm64/NatQ/KMulStep.lean — TIGHT COSTS] `karatsuba` (amd64): the member step of the multiplication SCC

`kar_step`: from the induction hypothesis below the measure `8·n + 2`, the summary of `karatsuba` (member `(.kar, a)`):
`kmPro` → `kSub1` → `kSub2` → `kS1` → `kS2` → `kS3` → `kA1` → `kA2` → `kEnd` (the three inner `(*Int).mul` calls use
the hypothesis). (Structure as this repo's amd64 `KSqrStep.ksqr_step`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem kbv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem kar_step (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (m : Nat) (ih : ∀ j, IH impl R H m j) (a : Args) :
    Summary (LibMul.program.link impl) (entryOf (.kar, a)) (fun s => preOf R H (.kar, a) s ∧ μ (.kar, a) s = m)
      (postOf R H (.kar, a)) := by
  intro s hpc ⟨⟨⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, y8, y16, y24⟩, hpre⟩, hμ⟩
  have hμ' : 8 * a.a8.toNat + 2 = m := hμ
  subst hμ'
  have hxl : a.a5.toNat = a.a8.toNat := hpre.2.2.2.2.2.2.1
  have hzl : a.a2.toNat = 2 * a.a8.toNat := hpre.2.2.2.2.2.2.2.1
  rw [hxl, hzl] at hpre
  show ReachesRet _ (retAddrOf s) s fun s' => Kept s s' ∧ KPost R a.b H a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat
    a.a4.toNat a.a5.toNat a.a7.toNat a.a8.toNat s s'
  rw [hxl, hzl]
  refine kmPro impl hap R hgr hmc hwb hpre hpc (by rw [h0, kbv_ofNat_toNat]) (by rw [h3, kbv_ofNat_toNat])
    (by rw [h1, ← hzl, kbv_ofNat_toNat]) (by rw [h7, kbv_ofNat_toNat]) (by rw [h6, kbv_ofNat_toNat])
    (by rw [h8, ← hxl, kbv_ofNat_toNat]) (by rw [h9, kbv_ofNat_toNat]) y8 y16 y24 hx15 hdf ?_
  intro S1 lx0 lx1 ly0 ly1 t Lk1 bk1 hB1
  refine kSub1 impl hap R hmk hmv hwb hx15 hdf S1 hB1 fun S2 Lk2 bk2 tng ltx hB2 => ?_
  refine kSub2 impl hap R hmk hmv hwb hx15 hdf S2 hB2 fun S3 Lk3 bk3 yng lty hB3 => ?_
  refine kS1 impl hap R hmc ih hx15 hdf S3 hB3 fun S4 Lk4 bk4 ng l1 hB4 => ?_
  refine kS2 impl R ih hx15 hdf S4 hB4 fun S5 Lk5 bk5 l0 hB5 => ?_
  refine kS3 impl R ih hx15 hdf S5 hB5 fun S6 Lk6 bk6 l2 hB6 => ?_
  refine kA1 impl hap R hmk hmv hwb hx15 hdf S6 hB6 fun S7 Lk7 bk7 ng' l hB7 => ?_
  refine kA2 impl hap R hmk hmv hwb hx15 hdf S7 hB7 fun S8 Lk8 bk8 l' hB8 => ?_
  exact kEnd impl hap R hmv hx15 hdf hra S8 hB8

end FvModexp.Amd64.Q.NatMul
