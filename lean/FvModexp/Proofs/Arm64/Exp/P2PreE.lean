import FvModexp.Proofs.Arm64.Exp.P2PreE1
import FvModexp.Proofs.Common.TruncMath

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (arm64): the entry segment (agent infra)

From the entry `0x1b53d0`: the stack-guard check, the frame (`MOVD.W R30, -208(RSP)`, FP at `SP - 216`), the
`windowSize` check (`TBNZ`, `len == 1 << windowSize`, else `gopanic`), the argument spills, `w = (logM + 63) >> 6`
and the call `stk.nat((len + 1) w)` (`callSN` → `FillJ 0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

theorem mul_ofNat64 (a c : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat} {mlC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segE (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsn : StackNatX.HypQ impl R ns stkS aboveS) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s)
    (hpc : s.pc = BitVec.ofNat 64 1790928) (h0 : s.regs 0 = BitVec.ofNat 64 st) (h1 : s.regs 1 = BitVec.ofNat 64 pw)
    (h2 : s.regs 2 = BitVec.ofNat 64 pl) (h4 : s.regs 4 = BitVec.ofNat 64 ws) (h5 : s.regs 5 = BitVec.ofNat 64 lm)
    (kF : FillJ impl R kc sqC mlC b L st pw pl lm x xl s 0) :
    Goal impl R kc sqC mlC b L st pw pl lm x xl s s := by
  have hsl0 := s.sp.isLt
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, hga, -, -, -⟩, -, -, hws, hplw, -, hlm, -, -, -, -, -, -, -, -,
    -, -, -, -, ⟨⟨hst8, -, -, hst48, -, -, -⟩, -, -, -⟩, -, -, -, -, -, -, -⟩ := id hpre
  simp only [K, A] at hb' ha hw hga hg3
  unfold Apart at hga
  have hst64 : st < 2 ^ 64 := by omega
  have hpw64 : pw < 2 ^ 64 := by have := (pf_of hpre (by omega)).pw48; omega
  have hlm64 : lm + 63 < 2 ^ 64 := by omega
  have hsh : BitVec.ofNat 64 (lm + 63) >>> 6 = BitVec.ofNat 64 (W lm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hlm64, Nat.mod_eq_of_lt (by simp only [W]; omega)]
  have hadd : BitVec.ofNat 64 lm + 63#64 = BitVec.ofNat 64 (lm + 63) := (BitVec.ofNat_add lm 63).symm
  have hpreH : Hide (Pre R kc sqC mlC b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hpre
  rcases hws with rfl | rfl
  · subst hplw
    have hmul : (5#64) * BitVec.ofNat 64 (W lm) = BitVec.ofNat 64 (NB (2 ^ 2) lm) := by
      rw [show (5#64) = BitVec.ofNat 64 5 from rfl, mul_ofNat64]
    unfold Goal
    janus_run [hadd, TruncMath.rot6, hsh, hmul] until [1784176]
    refine callSN hap hns hnf hsn hkS haS hkc hpreH.h kF ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_
    all_goals first | (simp only [winA, K, A]; janus_frame) | exact Expmc.sp_sub _ _ (by omega) (by omega) |
      (simp only [Sl]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp <;> exact Nat.mod_eq_of_lt (by simp only [W]; omega)) | janus_simp
  · subst hplw
    have hmul : (17#64) * BitVec.ofNat 64 (W lm) = BitVec.ofNat 64 (NB (2 ^ 4) lm) := by
      rw [show (17#64) = BitVec.ofNat 64 17 from rfl, mul_ofNat64]
    unfold Goal
    janus_run [hadd, TruncMath.rot6, hsh, hmul] until [1784176]
    refine callSN hap hns hnf hsn hkS haS hkc hpreH.h kF ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_
    all_goals first | (simp only [winA, K, A]; janus_frame) | exact Expmc.sp_sub _ _ (by omega) (by omega) |
      (simp only [Sl]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp <;> exact Nat.mod_eq_of_lt (by simp only [W]; omega)) | janus_simp

end

end FvModexp.Arm64.P2Pre
