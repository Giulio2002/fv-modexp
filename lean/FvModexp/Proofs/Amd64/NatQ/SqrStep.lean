import FvModexp.Proofs.Amd64.NatQ.SqrZero
import FvModexp.Proofs.Amd64.NatQ.SqrOneA
import FvModexp.Proofs.Amd64.NatQ.SqrMake
import FvModexp.Proofs.Amd64.NatQ.SqrBM
import FvModexp.Proofs.Amd64.NatQ.SqrBS
import FvModexp.Proofs.Amd64.NatQ.SqrKS

/-!
# [TIGHT COSTS, divmc s38] `nat.sqr` (amd64): the member step of the squaring SCC (twin of Arm64/NatQ/SqrStep)

`sqr_step`: for the measure `n`, from the induction hypothesis of every member below `n`, the summary of `nat.sqr`
(member `(false, a)`) at measure `n`: `n = 0` (`zero`), `n = 1` (`one_reuse` / `one_alloc`), `n ≥ 2` (`make_reuse` /
`make_alloc`, then `bm` / `bs` / `ks` by the thresholds).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

theorem sqr_step (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R H n j) (a : Args) :
    Summary (LibSqr.program.link impl) (entryOf (false, a)) (fun s => preOf R H (false, a) s ∧ μ (false, a) s = n)
      (postOf R H (false, a)) := by
  have c4 : CodeIn64 (Extracted.program.ofImpl impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibSqr.names
  have hmk' := MakesliceLiveContract64.of_codeIn c4 hmk
  intro s hpc ⟨⟨⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩, hpre⟩, hμ⟩
  show ReachesRet _ (retAddrOf s) s fun s' => Kept s s' ∧ SPost R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat
    a.a4.toNat a.a5.toNat a.a6.toNat s s'
  have hpc' : s.rip = BitVec.ofNat 64 0x5f0fe0 := hpc
  have hμ' : 2 * a.a5.toNat + 1 = n := hμ
  rcases Nat.lt_or_ge a.a5.toNat 2 with hx | hx
  · rcases Nat.lt_or_ge a.a5.toNat 1 with hx0 | hx1
    · exact zero impl R a.b a.L a.W _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre (by omega)
    · rcases Nat.lt_or_ge a.a2.toNat 2 with hz | hz
      · exact one_alloc impl R hmk' a.b a.L a.W _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre
          (by omega) hz
      · exact one_reuse impl R a.b a.L a.W _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre (by omega) hz
  have hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s p c L1 b1 S.mem →
      JoinAt s S p c a.a3 a.a4 a.a5 a.a6 → ReachesRet (LibSqr.program.link impl) (retAddrOf s) S fun s' =>
        Kept s s' ∧ SPost R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s s' := by
    intro p c L1 b1 S hJ hA
    rcases Nat.lt_or_ge a.a5.toNat 12 with h12 | h12
    · exact bm impl hap R hmc S hJ hA hx h12 hra hx15 hdf
    rcases Nat.lt_or_ge a.a5.toNat 80 with h80 | h80
    · exact bs impl hap R hgr hmc hwb S hJ hA h12 h80 hra hx15 hdf
    · exact ks impl R S hJ (fun a' => hμ' ▸ ih (true, a')) hA h80 hra hx15 hdf
  by_cases hr : 2 * a.a5.toNat ≤ a.a2.toNat ∧ a.a0.toNat + 8 * a.a2.toNat ≠ a.a4.toNat + 8 * a.a6.toNat
  · exact make_reuse impl R a.b a.L a.W _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre hx hr.1 hr.2 _ hK
  · exact make_alloc impl R hmk' a.b a.L a.W _ _ _ _ _ _ _ s hpc' h0 h3 h1 h7 h6 h8 h9 hpre hx (by omega) _ hK

end FvModexp.Amd64.Q.NatSqr
