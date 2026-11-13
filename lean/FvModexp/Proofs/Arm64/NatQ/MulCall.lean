import FvModexp.Proofs.Arm64.NatQ.MulRel
import FvModexp.Proofs.Arm64.NatQ.SqrCall

/-!
# [Q-form copy of Arm64/Nat/MulCall.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64): facts at `Core` for the callees (threshold, operand values, result separation)
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (apart_of_held winA_of_win)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}

/-- `karatsubaThreshold = 40` at `M` -/
theorem Core.thr (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) :
    M.readLE 7147144 8 = 40 ∧ M.accessible 7147144 8 false = true := by
  obtain ⟨-, -, -, ⟨h40, -, -, -, e40, -, -, hacc, hrt, hw, -⟩, -⟩ := hJ.pre
  have eg : RunIface.gA = 7147136 := rfl
  rw [eg] at e40 hacc hrt hw
  rw [e40] at h40
  simp only [win, outside_cons, outside_nil, and_true] at hw
  refine ⟨?_, ?_⟩
  · rw [hJ.rd (Or.inr (hrt.of_sub (by omega) (by omega)))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)]; exact h40
  · rw [hJ.F.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)

theorem Core.xv (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hx : 0 < xl) :
    natVal M xp xl = natVal s.mem xp xl := by
  obtain ⟨-, -, -, -, -, ⟨⟨hxlc, -, -, -, hxh, hxw⟩, -⟩, -⟩ := hJ.pre
  exact hJ.rd ((hxh (by omega)).1.sub (Nat.le_refl _) (by omega)) (hxw hx).1

theorem Core.yv (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hy : 0 < yl) :
    natVal M yp yl = natVal s.mem yp yl := by
  obtain ⟨-, -, -, -, -, ⟨-, ⟨hylc, -, -, -, hyh, hyw⟩, -⟩, -⟩ := hJ.pre
  exact hJ.rd ((hyh (by omega)).1.sub (Nat.le_refl _) (by omega)) (hyw hy).1

theorem Core.pg (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hc : 0 < c) :
    Apart p (8 * c) ((s.regs 28).toNat + 16) 8 := by
  obtain ⟨⟨-, -, -, -, -, hgr0, -⟩, -, -, -, -, ⟨-, -, ⟨-, -, -, hzg, -⟩, -⟩, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · exact (hzg hc).1
  · have := NatAdd.outside_of_inRanges hgr0 hin; unfold Apart; omega

/-- the result is apart from the stack's free part -/
theorem Core.pfree (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hc : 0 < c) :
    Apart p (8 * c) (BasicSqr.freeP s.mem st) (BasicSqr.freeN s.mem st) := by
  obtain ⟨-, -, -, -, -, ⟨-, -, ⟨-, -, -, hzs, -⟩, -⟩, ⟨-, -, -, -, -, -, -, -, -, hfh, -⟩, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, hap, -⟩
  · exact (hzs hc).2.2.1
  · exact apart_of_held hfh hin hap

/-- the result is apart from the threshold globals -/
theorem Core.pgA (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hc : 0 < c) :
    Apart p (8 * c) RunIface.gA 32 := by
  obtain ⟨-, -, -, ⟨-, -, -, -, -, -, -, -, hgrt, -⟩, -, ⟨-, -, ⟨-, -, -, hzs, -⟩, -⟩, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · exact (hzs hc).2.2.2
  · have := NatAdd.outside_of_inRanges hgrt hin; unfold Apart; omega

/-- the result array is apart from the stack header -/
theorem Core.pst (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hc : 0 < c) :
    Apart p (8 * c) st 24 := by
  obtain ⟨-, -, -, -, -, ⟨-, -, ⟨-, -, -, hzs, -⟩, -⟩, ⟨-, ⟨-, hsth, -⟩, -⟩, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, hap, -⟩
  · have := (hzs hc).2.1; unfold Apart at this ⊢; omega
  · exact apart_of_held hsth hin hap

/-- the stack header at a state reached from `M` by window stores -/
theorem Core.hdrS (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) {m : Memory}
    (hF : MemFrame M m (winA s W 88)) :
    stW m st = stW s.mem st ∧ stLen m st = stLen s.mem st ∧ stCap m st = stCap s.mem st := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have e : ∀ k, k + 8 ≤ 24 → m.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk => by
    rw [hF.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega), hJ.hdr k hk]
  have e0 := e 0 (by omega); simp only [Nat.add_zero] at e0
  exact ⟨e0, e 8 (by omega), e 16 (by omega)⟩

end

end FvModexp.Arm64.Q.NatMul
