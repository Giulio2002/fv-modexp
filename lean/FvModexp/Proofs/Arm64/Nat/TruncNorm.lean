import FvModexp.Proofs.Arm64.Nat.TruncDefs

/-!
# `nat.trunc` (arm64): the inlined `z.norm()` loop and the return (`+0x1b8`, `CMP $0, R1`; `R0 = p`, `R1 = i`, `R2 = c`)

`for i > 0 && z[i-1] == 0 { i-- }` (`+0x1b4 MOVD R3, R1` is the loop-back entry), `return z[0:i]`
(`CMP R2, R1; BHI panic`; `MOVD -8(RSP), R29; MOVD.P 112(RSP), R30; RET`). Memory is unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Trunc

abbrev hNorm : Nat := segAddr Extracted.program fn + 0x1b8

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (hal : s.sp.toNat % 16 = 0) (hsp0 : 4208 ≤ s.sp.toNat) (hsp1 : s.sp.toNat + 64 ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 4208) (4208 + 64) true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hNorm → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 2 = BitVec.ofNat 64 c → S.sp = s.sp - 112#64 →
      S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 120#64 → S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibTrunc.program.link impl) (s.regs 30) S fun s' =>
        (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h0 h2 hsp h28 h29 h18 hm hv
    have hc' : (c % 18446744073709551616) = c := Nat.mod_eq_of_lt (by omega)
    janus_run [hm, hr1, hr2, hc']
    refine hfin _ 0 rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h0 h2 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hc' : (c % 18446744073709551616) = c := Nat.mod_eq_of_lt (by omega)
    janus_run [hm, hr1, hr2, key, hc'] until [hNorm]
    · -- `z[i] = 0`: one more step down
      have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp)
        (by janus_simp) rfl ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      all_goals try janus_simp
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

end FvModexp.Arm64.Trunc
