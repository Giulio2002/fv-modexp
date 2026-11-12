import FvModexp.Proofs.Arm64.Exp.P2DEnt
import FvModexp.Proofs.Arm64.Exp.P2DPost
import FvModexp.Proofs.Arm64.Exp.P2DOneR

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `return z.setWord(0)` (`z[:0]`, nat.go:938 / nat.go:946) (agent infra)

`zeroP`: from `zeroE` (`0x1b5980`, even `x`, `len y > 1`) or `zero2` (`0x1b5a78`, `tz · y[0] ≥ logM` or overflow):
`R1 = 0`, epilogue; post `PostD` with value `0` (the caller proves `X^Y mod 2^logM = 0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

abbrev zero2 : Nat := 1792632

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem zeroR (impl : List Segment) (Q : State → Prop) (sp r29 ret pc : Nat) (M : Memory)
    (he : Epi M sp r29 ret) (hpc0 : pc = zeroE ∨ pc = zero2)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pc) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KF : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 112) → s'.regs 0 = S.regs 0 → s'.regs 1 = 0#64 →
      s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 → s'.regs 28 = S.regs 28 →
      s'.regs 29 = BitVec.ofNat 64 r29 → s'.mem = M → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, rfp, rlr, hr4, hr48⟩ := he
  generalize e0 : S.regs 0 = x0 at KF
  generalize e2 : S.regs 2 = x2 at KF
  generalize e18 : S.regs 18 = x18 at KF
  generalize e28 : S.regs 28 = x28 at KF
  subst hmem
  rcases hpc0 with rfl | rfl
  · janus_run [rfp, rlr]
    refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals janus_simp
  · janus_run [rfp, rlr]
    refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals janus_simp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`return z[:0]`** -/
theorem zeroP {impl : List Segment} (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk)
    (hA : 72 ≤ A) (hv0 : natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm = 0)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    {pc : Nat} (hpc0 : pc = zeroE ∨ pc = zero2) (S : State) (hpc : S.pc = BitVec.ofNat 64 pc)
    (esp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 112)) (e0 : S.regs 0 = BitVec.ofNat 64 zp)
    (e2 : S.regs 2 = BitVec.ofNat 64 zc) (e18 : S.regs 18 = s.regs 18)
    (e28 : S.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat)
    (hm : S.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  obtain ⟨hC, -⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hal, hle, h48, hacc⟩, -⟩, -⟩ := hC'
  generalize hSP : s.sp.toNat = SP at *
  have hsp1 : 8 ≤ SP - 112 := by omega
  have hepi : Epi (W0 s.mem (SP - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) (SP - 112)
      (s.regs 29).toNat (s.regs 30).toNat := by
    refine ⟨by omega, hsp1, by omega, ?_, w0_fp hsp1 (BitVec.isLt _), w0_lr hsp1 (BitVec.isLt _), hr4, hr48⟩
    simp only [W0, Memory.accessible_writeLE]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
  have hF0' : MemFrame s.mem (W0 s.mem (SP - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) (ownW s stk A) :=
    (w0_frame s.mem hsp1).mono fun a k ho => by
      simp only [ownW, hSP, outside_cons, outside_nil, and_true] at ho ⊢; omega
  rw [hv0, show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
  refine zeroR impl _ (SP - 112) _ _ pc _ hepi hpc0 S hpc esp hm fun s' a1 a2 a3 a4 a5 a6 a7 a8 => ⟨?_, a5.trans e18,
    a6.trans (e28.trans (by simp)), a7.trans (by simp), ?_⟩
  · rw [a1]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hSP]; omega
  · exact post_own hC (by omega) (zs := []) (by simpa only [List.append_nil] using hF0') (fun r hr => by simp at hr)
      (Nat.zero_le _) (by simp [natVal]) (Or.inl rfl) a8 (a2.trans e0) a3 (a4.trans e2)

end

end FvModexp.Arm64.P2D
