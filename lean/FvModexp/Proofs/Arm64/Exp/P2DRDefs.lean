import FvModexp.Proofs.Arm64.Exp.P2DT
import FvModexp.Proofs.Arm64.Exp.P2DEnt
import FvModexp.Proofs.Arm64.Exp.P2DStmt
import FvModexp.Proofs.Arm64.Exp.P2DTz
import FvModexp.Proofs.Arm64.Nat.RshDefs
import FvModexp.Proofs.Arm64.Nat.LshDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the even-base recursive path — shared facts (agent infra)

Frame base `sp = SP - 112`; the path's own slots (`W1`): `sp + 96` (`lo = tz·y[0]`), `sp + 120 … 200`; `rsh`/`lsh` run
with window `[sp - (stk - 112), sp + 88)` (`CEnv` from the entry `CPre`: `cenv_of`), the recursive call with
`[sp - (stk - 112), sp + 96)` (`cpre_sub`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the caller environment one frame down** (window `[SP - stk, SP - 24)` at `sp = SP - 112`) -/
theorem cenv_of (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {M : Memory}
    (hF : MemFrame s.mem M (R.rt ++ ownW s stk A)) (hrg : M.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1) (hk : 112 ≤ stk) :
    CallW.CEnv R L1 (s.regs 28).toNat (s.sp.toNat - 112) (stk - 112) 88 M := by
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, hd, hwrt, hgw, hgrt, hLs, hro'⟩, -, -, hro, -⟩ := hP
  generalize hSP : s.sp.toNat = SP at *
  have hout : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hgow : Outside ((s.regs 28).toNat + 16) 8 (ownW s stk A) := by
    simp only [ownW, outside_cons, outside_nil, and_true, hSP]; unfold Apart at hgw; omega
  have hgM : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hgow⟩)
  refine ⟨by omega, by omega, by omega, by
      rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega),
    g1, by rw [hF.accessible]; exact g2, by rw [hgM]; omega, hout.of_sub (by omega) (by omega),
    by unfold Apart at hgw ⊢; omega, hgrt, ?_,
    dataLoaded_frame hd hrg hro hF (fun r hr _ => by
      simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)), hro'⟩
  refine hx.liveSep (fun r hr => ?_) fun r hr => ?_
  · have := hLs r hr
    simp only [win, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  · simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)

end

end FvModexp.Arm64.P2D
