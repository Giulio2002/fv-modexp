import FvModexp.Proofs.Arm64.Nat.SqrZero
import FvModexp.Proofs.Arm64.Nat.SqrOne
import FvModexp.Proofs.Arm64.Nat.SqrMake
import FvModexp.Proofs.Arm64.Nat.SqrBM
import FvModexp.Proofs.Arm64.Nat.SqrBS
import FvModexp.Proofs.Arm64.Nat.SqrKS

/-!
# `nat.sqr` (arm64): the member step of the squaring SCC

`sqr_step`: for the measure `n`, from the induction hypothesis of every member below `n`, the summary of `nat.sqr`
(member `(false, a)`) at measure `n`: `n = 0` (`zero`), `n = 1` (`one_reuse` / `one_alloc`), `n ≥ 2` (`make_reuse` /
`make_alloc`, then `bm` / `bs` / `ks` by the thresholds).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatSqr

theorem sqr_step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R n j) (a : Args) :
    Summary (LibSqr.program.link impl) (entryOf (false, a)) (fun s => preOf R (false, a) s ∧ μ (false, a) s = n)
      (postOf R (false, a)) := by
  have c4 : CodeIn (Extracted.program.ofImpl impl) (LibSqr.program.link impl) := by
    rw [LibSqr.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibSqr.names
  have hmk' := MakesliceLiveContract.of_codeIn c4 hmk
  intro s hpc ⟨⟨⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6⟩, hpre⟩, hμ⟩
  show ReachesRet _ (s.regs 30) s fun s' => Kept s s' ∧ SPost R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat
    a.a4.toNat a.a5.toNat a.a6.toNat s s'
  have hpc' : s.pc = BitVec.ofNat 64 0x1bb420 := hpc
  have hμ' : 2 * a.a5.toNat + 1 = n := hμ
  rcases Nat.lt_or_ge a.a5.toNat 2 with hx | hx
  · rcases Nat.lt_or_ge a.a5.toNat 1 with hx0 | hx1
    · exact zero impl R a.b a.L a.W _ _ _ _ _ _ _ s hpc' hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre (by omega)
    · rcases Nat.lt_or_ge a.a2.toNat 2 with hz | hz
      · exact one_alloc impl R hmk' a.b a.L a.W _ _ _ _ _ _ _ s hpc' hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre (by omega) hz
      · exact one_reuse impl R a.b a.L a.W _ _ _ _ _ _ _ s hpc' hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre (by omega) hz
  have hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s p c L1 b1 S.mem →
      JoinAt s S p c a.a3 a.a4 a.a5 a.a6 → ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' =>
        Kept s s' ∧ SPost R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat s s' := by
    intro p c L1 b1 S hJ hA
    rcases Nat.lt_or_ge a.a5.toNat 12 with h12 | h12
    · exact bm impl hap R hmc S hJ hA hx h12 hl4 hl48
    rcases Nat.lt_or_ge a.a5.toNat 80 with h80 | h80
    · exact bs impl hap R hgr hmc hwb S hJ hA h12 h80 hl4 hl48
    · exact ks impl R S hJ (fun a' => hμ' ▸ ih (true, a')) hA h80 hl4 hl48
  by_cases hr : 2 * a.a5.toNat ≤ a.a2.toNat ∧ a.a0.toNat + 8 * a.a2.toNat ≠ a.a4.toNat + 8 * a.a6.toNat
  · exact make_reuse impl R a.b a.L a.W _ _ _ _ _ _ _ s hpc' h0 h1 h2 h3 h4 h5 h6 hpre hx hr.1 hr.2 _ hK
  · exact make_alloc impl R hmk' a.b a.L a.W _ _ _ _ _ _ _ s hpc' h0 h1 h2 h3 h4 h5 h6 hpre hx (by omega) _ hK

end FvModexp.Arm64.NatSqr
