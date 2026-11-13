import FvModexp.Proofs.Amd64.NatQ.MulZero
import FvModexp.Proofs.Amd64.NatQ.MulOne
import FvModexp.Proofs.Amd64.NatQ.MulMakeR
import FvModexp.Proofs.Amd64.NatQ.MulMakeA
import FvModexp.Proofs.Amd64.NatQ.MulBM
import FvModexp.Proofs.Amd64.NatQ.MulSwap
import FvModexp.Proofs.Amd64.NatQ.MulLoopPath
import FvModexp.Proofs.Amd64.NatQ.MulKar

set_option autoImplicit false

/-!
# [amd64 port (divmc s53) of the Q-form Arm64/NatQ/MulStep.lean — TIGHT COSTS] `nat.mul` (amd64): the member step of the multiplication SCC (natmul.go:16-75)

`mul_step`: from the induction hypothesis below the measure `μl xl yl + 3`, the summary of `nat.mul` (member `(.mul, a)`):
`m < n` → `swap` (self-call); `n = 0` → `zero`; `n = 1` → `one` (`mulAddWW`); otherwise `make` (reuse or allocate) to the
join, then `basicMul` (`n < 40`), the karatsuba loop (`n < m`) or one `karatsuba` (`m = n`).
(Structure as this repo's amd64 `SqrStep.sqr_step`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem mul_step (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R H n j) (a : Args) :
    Summary (LibMul.program.link impl) (entryOf (.mul, a)) (fun s => preOf R H (.mul, a) s ∧ μ (.mul, a) s = n)
      (postOf R H (.mul, a)) := by
  have c4 : CodeIn64 (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibMul.names
  have hmk' := MakesliceLiveContract64.of_codeIn c4 hmk
  intro s hpc ⟨⟨⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, y1, y2, y3⟩, hpre⟩, hμ⟩
  show ReachesRet _ (retAddrOf s) s fun s' => Kept s s' ∧ MPost R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat
    a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat a.a9.toNat s s'
  have hpc' : s.rip = BitVec.ofNat 64 0x5f0840 := hpc
  have hμ' : μl a.a5.toNat a.a8.toNat + 3 = n := hμ
  rcases Nat.lt_or_ge a.a5.toNat a.a8.toNat with hlt | hyx
  · exact swap impl R n ih a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 y1 y2 y3 hpre
      hμ' hlt
  rcases Nat.lt_or_ge a.a8.toNat 1 with hy0 | hy1
  · exact zero impl R a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 y1 y2 y3 hpre
      (by omega)
  rcases Nat.lt_or_ge a.a8.toNat 2 with hy1' | hy2
  · exact one impl hap R hmk a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 y1 y2 y3 hpre
      (by omega) hyx
  have hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat
        a.a9.toNat s p c L1 b1 S.mem →
      JoinAt s S p c a.a3 a.a4 a.a5 a.a6 a.a7 a.a8 a.a9 → ReachesRet (LibMul.program.link impl) (retAddrOf s) S
        fun s' => Kept s s' ∧ MPost R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat
          a.a7.toNat a.a8.toNat a.a9.toNat s s' := by
    intro p c L1 b1 S hJ hA
    rcases Nat.lt_or_ge a.a8.toNat 40 with h40 | h40
    · exact bm impl hap R hmc S hJ hA hy2 hyx h40 hra hx15 hdf
    rcases Nat.lt_or_ge a.a8.toNat a.a5.toNat with hl | he
    · exact mloop impl hap R hmv hgr hmc hwb n (fun a' => ih (.kar, a')) (fun a' => ih (.mul, a')) S hJ hA h40 hl
        (by omega) hra hx15 hdf
    · exact karEq impl R n S hJ (fun a' => ih (.kar, a')) hA h40 (by omega)
        (by simp only [μl] at hμ'; split at hμ' <;> omega) hra hx15 hdf
  by_cases hr : a.a5.toNat + a.a8.toNat ≤ a.a2.toNat ∧ a.a0.toNat + 8 * a.a2.toNat ≠ a.a4.toNat + 8 * a.a6.toNat ∧
      a.a0.toNat + 8 * a.a2.toNat ≠ a.a7.toNat + 8 * a.a9.toNat
  · exact make_reuse impl R a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 y1 y2 y3 hpre
      hy2 hyx hr.1 hr.2.1 hr.2.2 _ hK
  · exact make_alloc impl R hmk' a.b a.L a.W _ _ _ _ _ _ _ _ _ _ s hpc' h0 h3 h1 h7 h6 h8 h9 y1 y2 y3 hpre hy2 hyx
      (by omega) _ hK

end FvModexp.Amd64.Q.NatMul
