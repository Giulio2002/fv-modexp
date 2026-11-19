import FvModexp.Proofs.Amd64.Exp.P2PreJ
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the entry segment (agent divmc s61; twin of `Arm64/Exp/P2PreE`)

From the entry `0x5e8900`: the stack-growth check (falls through: `StackGuardOK`), `PUSHQ BP; SUBQ $0xa8, SP`, the spills,
the misuse check `len(powers) == 1 << windowSize` (`windowSize ∈ {2, 4}` concrete), `w = (logM + 63) >> 6`, the locals,
`RBX = (len + 1) w` and the call of `(*stack).nat` → `JN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

theorem shr6 (lm : Nat) (h : lm ≤ 2 ^ 13) : (BitVec.ofNat 64 lm + 63#64) >>> 6 = BitVec.ofNat 64 (W lm) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [W]; omega

theorem mul_ofNat64 (a c : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem entry (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl pc ws lm x xl xc : Nat) (s : State) (hkc : 8 ≤ kc)
    (hpc : s.rip = BitVec.ofNat 64 0x5e8900)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h3 : s.regs 3 = BitVec.ofNat 64 pw) (h1 : s.regs 1 = BitVec.ofNat 64 pl)
    (_h7 : s.regs 7 = BitVec.ofNat 64 pc) (h6 : s.regs 6 = BitVec.ofNat 64 ws) (h8 : s.regs 8 = BitVec.ofNat 64 lm)
    (h9 : s.regs 9 = BitVec.ofNat 64 x) (h10 : s.regs 10 = BitVec.ofNat 64 xl) (h11 : s.regs 11 = BitVec.ofNat 64 xc)
    (hpre : Pre R kc b L st pw pl ws lm x xl s)
    (kN : JN impl R kc b L st pw pl ws lm x xl s) :
    Goal impl R kc b L st pw pl lm x xl s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB, _⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, hws, hplw, hlm2, hlm, -, hpw48, -,
    -, -, -, -, -, -, ⟨-, -, hx48, -, -⟩, -, -, -, ⟨-, ⟨-, -, -, hst48, -⟩, -⟩, -⟩ := hpre'
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hgB hb' ha hga hgN hgR
  have hst64 : st < 2 ^ 64 := by omega
  have hpw64 : pw < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  have hsh := shr6 lm hlm
  have hW := w_facts hpre
  have hpl := pl_facts hpre
  unfold Goal
  rcases hws with rfl | rfl
  · subst hplw
    have hmul : BitVec.ofNat 64 (W lm) * 5#64 = BitVec.ofNat 64 (NB (2 ^ 2) lm) := by
      rw [show (5#64) = BitVec.ofNat 64 5 from rfl, mul_ofNat64]; simp only [NB]; rw [Nat.mul_comm]
    have h6' : s.regs 6 = 2#64 := h6
    have h1' : s.regs 1 = 4#64 := h1
    have hm2 : (2#64).msb = false := by decide
    janus64_run [h6', h1', hsh, hmul, hm2] until [snE]
    refine kN _ hpre rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · janus64_simp; exact Expmc.sp_sub _ _ (by omega) (by omega)
    · janus64_simp; exact Expmc.sp_sub _ _ (by omega) (by omega)
    · janus64_simp
    · rfl
    · rfl
    · rfl
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · simp only [win, K, A]; janus_frame
    · janus64_simp
    · janus64_simp
    all_goals janus64_simp
  · subst hplw
    have hmul : BitVec.ofNat 64 (W lm) * 17#64 = BitVec.ofNat 64 (NB (2 ^ 4) lm) := by
      rw [show (17#64) = BitVec.ofNat 64 17 from rfl, mul_ofNat64]; simp only [NB]; rw [Nat.mul_comm]
    have h6' : s.regs 6 = 4#64 := h6
    have h1' : s.regs 1 = 16#64 := h1
    have hm2 : (4#64).msb = false := by decide
    janus64_run [h6', h1', hsh, hmul, hm2] until [snE]
    refine kN _ hpre rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · janus64_simp; exact Expmc.sp_sub _ _ (by omega) (by omega)
    · janus64_simp; exact Expmc.sp_sub _ _ (by omega) (by omega)
    · janus64_simp
    · rfl
    · rfl
    · rfl
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · simp only [win, K, A]; janus_frame
    · janus64_simp
    · janus64_simp
    all_goals janus64_simp

end FvModexp.Amd64.P2Pre
