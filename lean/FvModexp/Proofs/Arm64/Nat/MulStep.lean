import FvModexp.Proofs.Arm64.Nat.MulZero
import FvModexp.Proofs.Arm64.Nat.MulOne
import FvModexp.Proofs.Arm64.Nat.MulMake
import FvModexp.Proofs.Arm64.Nat.MulBM
import FvModexp.Proofs.Arm64.Nat.MulSwap
import FvModexp.Proofs.Arm64.Nat.MulLoopPath

/-!
# `nat.mul` (arm64): the member step of the multiplication SCC

`mul_step`: for the measure `n`, from the induction hypothesis of every member below `n`, the summary of `nat.mul`
(member `(.mul, a)`) at measure `n` (natmul.go:16-62): `m < n` (`swap`), `n = 0` (`zero`), `n = 1` (`one`),
`n ≥ 2` (`make_reuse` / `make_alloc`, then `bm` (`n < 40`) / `karEq` (`40 ≤ n = m`) / `mloop` (`40 ≤ n < m`)).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatMul

theorem mul_step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R n j) (a : Args) :
    Summary (LibMul.program.link impl) (entryOf (.mul, a)) (fun s => preOf R (.mul, a) s ∧ μ (.mul, a) s = n)
      (postOf R (.mul, a)) := by
  have c4 : CodeIn (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibMul.names
  have hmk' := MakesliceLiveContract.of_codeIn c4 hmk
  intro s hpc ⟨⟨⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hpre⟩, hμ⟩
  show ReachesRet _ (s.regs 30) s fun s' => Kept s s' ∧ MPost R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat
    a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat a.a9.toNat s s'
  have hpc' : s.pc = BitVec.ofNat 64 0x1bae70 := hpc
  have hμ' : μl a.a5.toNat a.a8.toNat + 3 = n := hμ
  rcases Nat.lt_or_ge a.a5.toNat a.a8.toNat with hlt | hyx
  · exact swap impl R n ih a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre hμ' hlt
  rcases Nat.lt_or_ge a.a8.toNat 1 with hy0 | hy1
  · exact zero impl R a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre (by omega)
  rcases Nat.lt_or_ge a.a8.toNat 2 with hy1' | hy2
  · exact one impl hap R hmk a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre
      (by omega) hyx
  have hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat
        a.a9.toNat s p c L1 b1 S.mem →
      JoinAt s S p c a.a3 a.a4 a.a5 a.a6 a.a7 a.a8 a.a9 → ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
        Kept s s' ∧ MPost R a.b a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat
          a.a8.toNat a.a9.toNat s s' := by
    intro p c L1 b1 S hJ hA
    rcases Nat.lt_or_ge a.a8.toNat 40 with h40 | h40
    · exact bm impl hap R hmc S hJ hA hy2 hyx h40 hl4 hl48
    rcases Nat.lt_or_ge a.a8.toNat a.a5.toNat with hl | he
    · exact mloop impl hap R hmv hgr hmc hwb n (fun a' => ih (.kar, a')) (fun a' => ih (.mul, a')) S hJ hA h40 hl
        (by omega) hl4 hl48
    · exact karEq impl R n (fun a' => ih (.kar, a')) S hJ hA h40 (by omega)
        (by simp only [μl] at hμ'; split at hμ' <;> omega) hl4 hl48
  by_cases hr : a.a5.toNat + a.a8.toNat ≤ a.a2.toNat ∧ a.a0.toNat + 8 * a.a2.toNat ≠ a.a4.toNat + 8 * a.a6.toNat ∧
      a.a0.toNat + 8 * a.a2.toNat ≠ a.a7.toNat + 8 * a.a9.toNat
  · exact make_reuse impl R a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre hy2 hyx hr.1
      hr.2.1 hr.2.2 _ hK
  · exact make_alloc impl R hmk' a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre hy2 hyx
      (by omega) _ hK

end FvModexp.Arm64.NatMul
