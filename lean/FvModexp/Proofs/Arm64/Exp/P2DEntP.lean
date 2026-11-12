import FvModexp.Proofs.Arm64.Exp.P2DEnt

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `ent` from the function's precondition `PreD` (agent infra)

`entP`: the entry state `s` (`pc = fnE`, `Regs`, `PreD` with window `[SP - stk, SP + A)`, `72 ≤ A`, `4320 ≤ stk`) reaches
`Q` when each of the four branch continuations of `ent` does (frame base `SP - 112`, memory `W0 s.mem …`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`ent` from `PreD`** -/
theorem entP (impl : List Segment) (Q : State → Prop) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat} (s : State)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hpc : s.pc = BitVec.ofNat 64 fnE) (hR : Regs s zp zl zc st xp xl xc yp yl yc lm)
    (K1 : lm = 1 → ∀ S' : State, S'.pc = BitVec.ofNat 64 oneE →
      RE S' (s.sp.toNat - 112) (s.regs 28).toNat zp zl zc st xp xl xc yp yl yc lm (s.regs 18) →
      S'.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp →
      ReachesRet (LibW.program.link impl) (s.regs 30) S' Q)
    (K2 : ¬lm = 1 → s.mem.readLE xp 8 % 2 = 1 → ∀ S' : State, S'.pc = BitVec.ofNat 64 oddE →
      RE S' (s.sp.toNat - 112) (s.regs 28).toNat zp zl zc st xp xl xc yp yl yc lm (s.regs 18) →
      S'.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp →
      ReachesRet (LibW.program.link impl) (s.regs 30) S' Q)
    (K3 : ¬lm = 1 → s.mem.readLE xp 8 % 2 = 0 → 1 < yl → ∀ S' : State, S'.pc = BitVec.ofNat 64 zeroE →
      RE S' (s.sp.toNat - 112) (s.regs 28).toNat zp zl zc st xp xl xc yp yl yc lm (s.regs 18) →
      S'.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp →
      ReachesRet (LibW.program.link impl) (s.regs 30) S' Q)
    (K4 : ¬lm = 1 → s.mem.readLE xp 8 % 2 = 0 → yl = 1 → ∀ S' : State, S'.pc = BitVec.ofNat 64 tzH →
      RE S' (s.sp.toNat - 112) (s.regs 28).toNat zp zl zc st xp xl xc yp yl yc lm (s.regs 18) →
      S'.regs 11 = 0#64 →
      S'.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp →
      ReachesRet (LibW.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibW.program.link impl) (s.regs 30) s Q := by
  obtain ⟨hC, hX, hY, -, hlm, -, -⟩ := hP
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, -, -, -, -, -, -⟩, -, -, -, -, -, -, hins, -⟩ := hC
  obtain ⟨⟨-, hxa, hx48, -, hxw⟩, hxn, -⟩ := hins xp xl (by simp)
  obtain ⟨⟨-, hya, hy48, -, hyw⟩, hyn, -⟩ := hins yp yl (by simp)
  generalize hSP : s.sp.toNat = SP at *
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  have hsp : s.sp = BitVec.ofNat 64 (SP - 112 + 112) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hSP]; omega
  simp only [win, hSP, outside_cons, outside_nil, and_true] at hxw hyw
  refine ent impl (s.regs 30) Q (SP - 112) (s.regs 28).toNat zp zl zc st xp xl xc yp yl yc lm (s.regs 29)
    (s.regs 30) s.mem (by omega) (by omega) (by omega)
    (Memory.accessible_mono _ hacc (by omega) (by omega)) g1 g2 (by omega) hyl0 (by omega)
    (fun h1 => by subst h1; simpa [natVal] using (Nat.pos_iff_ne_zero.1 hY))
    (Memory.accessible_weaken _ (Memory.accessible_mono _ hya (Nat.le_refl _) (by omega))) (by omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega) hxl0 (by omega)
    (Memory.accessible_weaken _ (Memory.accessible_mono _ hxa (Nat.le_refl _) (by omega))) (by omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega) s hpc hsp hR (by simp) rfl rfl rfl
    K1 K2 K3 K4

end FvModexp.Arm64.P2D
