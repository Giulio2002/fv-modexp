import FvModexp.Proofs.Arm64.Exp.P2W2Cp4

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): from the table to the loop test (agent infra)

`afterT`: from `AT` at `1795572`: skip loop (`afterTable`; `return 1` closed) and the first window (`blH`); the
continuation is the loop invariant's `KL` for every `kk` with the target value `x^y mod 2^logM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

theorem skipZero_le (y : Nat) : ∀ i yi i' yi', Exp.skipZero y i yi = some (i', yi') → i' ≤ i := by
  intro i
  induction i with
  | zero => intro yi i' yi' h; unfold Exp.skipZero at h; split at h <;> simp_all
  | succ i ih =>
    intro yi i' yi' h
    unfold Exp.skipZero at h
    split at h
    · simp at h; omega
    · have := ih _ _ _ h; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem afterT {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract (LibW.program.link impl) noE 4096 R)
    (hmv : MemmoveLive (LibW.program.link impl) P2Pre.mvE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L3 : List (Nat × Nat)} {b3 zzp bp : Nat}
    (hAT : AT R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M L3 b3 zzp bp)
    {sqC : Nat → Nat} {mlC : Nat → Nat → Nat} {c0 cst : Nat}
    (hb3 : b - c0 ≤ b3) (hcst : c0 + allocCost 8 ≤ cst) (hcb : cst ≤ b)
    (hcst2 : c0 + 2 * P2Pre.tC lm + 32 * min yl ((lm - 2) / 64 + 1) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm ≤ cst)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (hX : natVal s.mem xp xl % 2 = 1) (hY : 0 < natVal s.mem yp yl) (r29 : BitVec 64)
    (KL : ∀ kk, KL impl (s.regs 30) (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s)
      R b L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s r29 sqC mlC zzp bp kk cst
      (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1795572) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s) := by
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.2.1
  have hyN : NatNorm s.mem yp yl := hP.2.2.2.2.2.2.2.2.2.2.1
  refine afterTable hap hmk hno hP hAT hb3 hcst hcb hr4 hr48 hX hY r29 S hpc hsp h28 h29 h18 hm ?_
  intro S' i yi e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 hi hyi0 hyi hv
  have hii := skipZero_le _ _ _ _ _ hv
  have hi0 : i ≤ min (yl - 1) ((lm - 2) / 64) := by simp only [i0] at hii; omega
  have hyl : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  obtain ⟨hk1, hk32, -⟩ := kk_facts yi hyi0 hyi
  have hmul : (kkOf yi - 1 + 32 * i) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm ≤
      32 * min yl ((lm - 2) / 64 + 1) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm :=
    Nat.mul_le_mul_right _ (by omega)
  refine blH hmv hmk _ _ hP KL (CPF.ofAT hAT) S' i yi e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 hi hyi0 hyi hX
    (by omega) (by omega) ?_
  rw [← Exp.p2win_correct 2 lm _ _ (Or.inl rfl) hX hY hlm2, p2win_eq lm yl _ _ (SubMod2N.norm_nlen _ _ _ hyN), hv]
  simp only [Exp.winRun, Exp.B, kkOf, stp, show (64 : Nat) / 2 = 32 by rfl, show (2 : Nat) - 1 = 1 by rfl]

end

end FvModexp.Arm64.P2W2
