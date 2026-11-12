import FvModexp.Proofs.Arm64.Exp.P2DRec
import FvModexp.Proofs.Arm64.Exp.P2DOneR

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): runs around `return z.lsh(z, lo)` (nat.go:955; agent infra)

`runL`: `recR` → `lsh`'s entry (`R3..R5 := R0..R2`, `R6 := [sp + 96] = lo`, `R30 = lshR`); `epiL`: `lshR` → `RET`
(`R29 := [sp - 8]`, `SP += 112`, `R0..R2` = `lsh`'s result).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

abbrev lshR : Nat := 1792792
abbrev lshE : Nat := 1784560

theorem lsh_a : segAddr Extracted.program Lsh.fn = lshE := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `recR` → `nat.lsh`'s entry -/
theorem runL {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp lo : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 104 ≤ 2 ^ 48) (hacc : M.accessible (sp + 96) 8 false = true)
    (h96 : M.readLE (sp + 96) 8 = lo)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 recR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 lshE → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 0 →
      S'.regs 4 = S.regs 1 → S'.regs 5 = S.regs 2 → S'.regs 6 = BitVec.ofNat 64 lo →
      S'.regs 30 = BitVec.ofNat 64 lshR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at K
  generalize e1 : S.regs 1 = x1 at K
  generalize e2 : S.regs 2 = x2 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [h96, hacc, hal] until [lshE]
  refine K _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the epilogue after `lsh` -/
theorem epiL (impl : List Segment) (Q : State → Prop) (sp r29 ret : Nat) (M : Memory)
    (he : Epi M sp r29 ret)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 lshR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KF : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 112) → s'.regs 0 = S.regs 0 → s'.regs 1 = S.regs 1 →
      s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 → s'.regs 28 = S.regs 28 →
      s'.regs 29 = BitVec.ofNat 64 r29 → s'.mem = M → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, rfp, rlr, hr4, hr48⟩ := he
  generalize e0 : S.regs 0 = x0 at KF
  generalize e1 : S.regs 1 = x1 at KF
  generalize e2 : S.regs 2 = x2 at KF
  generalize e18 : S.regs 18 = x18 at KF
  generalize e28 : S.regs 28 = x28 at KF
  subst hmem
  janus_run [rfp, rlr]
  refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals janus_simp

end FvModexp.Arm64.P2D
