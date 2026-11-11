import FvModexp.Proofs.Arm64.Nat.NatSubDefs

/-!
# `nat.sub` (arm64): the `z.norm()` loop and the return (`+0x23c`, `CMP $0, R4`; `R4 = i`, `R0 = p`)

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]` (cap reloaded from `104(RSP') = SP - 56`). Memory is unchanged in the loop.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSub

abbrev hNorm : Nat := segAddr Extracted.program fn + 0x23c

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem norm (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → (s'.regs 0).toNat = p → (s'.regs 1).toNat = n' →
      (s'.regs 2).toNat = c → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat)
    (hr3 : M.readLE (s.sp.toNat - 56) 8 = c) (hal : s.sp.toNat % 16 = 0) (hsp0 : 4304 ≤ s.sp.toNat) (hsp1 : s.sp.toNat + 80 ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 4304) (4304 + 80) true = true) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hNorm → S.regs 4 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.sp = s.sp - 160#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 168#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibNatSub.program.link impl) (s.regs 30) S fun s' =>
        (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h3 h4 hsp h28 h29 h18 hm hv
    janus_run [hm, hr1, hr2, hr3]
    refine hfin _ 0 rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals janus_simp
    all_goals omega
  | succ i ih =>
    intro S hi hpc h3 h4 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, hr1, hr2, hr3, key] until [hNorm]
    · -- `z[i] = 0`: one more step down
      have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

end FvModexp.Arm64.NatSub
