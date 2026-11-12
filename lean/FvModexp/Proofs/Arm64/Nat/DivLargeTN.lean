import FvModexp.Proofs.Arm64.Nat.DivLargeDRel

/-!
# `divLarge` (arm64): the two inlined `norm()` loops of the tail (pattern of `Rsh.norm`)

`q = q.norm()` (natdiv.go:632): head `fn + 0x45c` (`CMP $0, R1`, `R0` = array, `R1` = length), exit `fn + 0x470`.
`r = u.norm()` (natdiv.go:638): head `fn + 0x4bc` (`CMP $0, R4`, `R0` = array, `R4` = length), exit `fn + 0x4d0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

abbrev qHead : Nat := segAddr Extracted.program fn + 0x45c
abbrev qExit : Nat := segAddr Extracted.program fn + 0x470
abbrev rHead : Nat := segAddr Extracted.program fn + 0x4bc
abbrev rExit : Nat := segAddr Extracted.program fn + 0x4d0

theorem natVal_drop_zero' {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `q.norm()`: from the loop head with length `i` to the exit with the normalised length `n' ≤ i` -/
theorem qnorm (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (SP G F X : W64) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 qExit → s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p →
      s'.regs 1 = BitVec.ofNat 64 n' → s'.sp = SP → s'.regs 28 = G → s'.regs 29 = F → s'.regs 18 = X → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → ReachesRet (LibDivL.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 qHead → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.sp = SP → S.regs 28 = G → S.regs 29 = F → S.regs 18 = X → S.mem = M →
      natVal M p i = V → ReachesRet (LibDivL.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h0 hsp h28 h29 h18 hm hv
    janus_run [hm] until [qExit]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h0 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [qHead, qExit]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero' hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      all_goals try janus_simp
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u.norm()`: from the loop head with length `i` (in `R4`) to the exit with the normalised length `n' ≤ i` -/
theorem rnorm (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (SP G F X : W64) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 rExit → s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p →
      s'.regs 4 = BitVec.ofNat 64 n' → s'.sp = SP → s'.regs 28 = G → s'.regs 29 = F → s'.regs 18 = X → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → ReachesRet (LibDivL.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 rHead → S.regs 4 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.sp = SP → S.regs 28 = G → S.regs 29 = F → S.regs 18 = X → S.mem = M →
      natVal M p i = V → ReachesRet (LibDivL.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h0 hsp h28 h29 h18 hm hv
    janus_run [hm] until [rExit]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h0 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [rHead, rExit]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero' hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      all_goals try janus_simp
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

end FvModexp.Arm64.DivLarge
