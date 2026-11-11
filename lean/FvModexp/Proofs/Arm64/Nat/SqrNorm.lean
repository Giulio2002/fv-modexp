import FvModexp.Proofs.Arm64.Nat.SqrRel

/-!
# `nat.sqr` (arm64): the four inlined `z.norm()` loops and the returns

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]`; the result is stored to `120..143(SP')` (`SP' = SP - 176`) and
returned in `X0..X2`. `norm1` (after `n = 1`, `+0x344`: `R0 = p`, `R1 = i`, `R2 = cap`), `normM` (after `basicMul`,
`+0x304`: cap reloaded from `88(SP')`), `normS` / `normK` (after `basicSqr` / `karatsubaSqr`, `+0x2a8` / `+0x24c`:
`R1 = p`, `R2 = i`, cap from `88(SP')`, defer bit `87(SP')` clear).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

abbrev hnorm1 : Nat := 0x1bb764

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm1 (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [(s.sp.toNat - 56, s.sp.toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' → s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hal : s.sp.toNat % 16 = 0) (hsp0 : 184 ≤ s.sp.toNat) (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 184) 184 true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hnorm1 → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 2 = BitVec.ofNat 64 c → S.sp = s.sp - 176#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 184#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h4 h2 hsp h28 h29 h18 hm hv
    janus_run [hm, hr1, hr2]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h4 h2 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, hr1, hr2, key] until [hnorm1]
    · -- `z[i] = 0`: one more step down
      have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ hi hv (Or.inr ?_)⟩
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

abbrev hnormM : Nat := 0x1bb724

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normM (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [(s.sp.toNat - 56, s.sp.toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' → s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hr3 : M.readLE (s.sp.toNat - 88) 8 = c) (hal : s.sp.toNat % 16 = 0) (hsp0 : 184 ≤ s.sp.toNat) (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 184) 184 true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hnormM → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.sp = s.sp - 176#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 184#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h4 hsp h28 h29 h18 hm hv
    janus_run [hm, hr1, hr2, hr3]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h4 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, hr1, hr2, hr3, key] until [hnormM]
    · -- `z[i] = 0`: one more step down
      have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ hi hv (Or.inr ?_)⟩
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

abbrev hnormS : Nat := 0x1bb6c8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normS (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [(s.sp.toNat - 56, s.sp.toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' → s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hr3 : M.readLE (s.sp.toNat - 88) 8 = c) (hb : M.readLE (s.sp.toNat - 89) 1 = 0) (hal : s.sp.toNat % 16 = 0) (hsp0 : 184 ≤ s.sp.toNat) (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 184) 184 true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hnormS → S.regs 2 = BitVec.ofNat 64 i →
      S.regs 1 = BitVec.ofNat 64 p → S.sp = s.sp - 176#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 184#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h4 hsp h28 h29 h18 hm hv
    janus_run [hm, hr1, hr2, hr3, hb]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h4 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, hr1, hr2, hr3, hb, key] until [hnormS]
    · -- `z[i] = 0`: one more step down
      have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ hi hv (Or.inr ?_)⟩
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

abbrev hnormK : Nat := 0x1bb66c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normK (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [(s.sp.toNat - 56, s.sp.toNat - 32)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' → s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat)
    (hr3 : M.readLE (s.sp.toNat - 88) 8 = c) (hb : M.readLE (s.sp.toNat - 89) 1 = 0) (hal : s.sp.toNat % 16 = 0) (hsp0 : 184 ≤ s.sp.toNat) (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 184) 184 true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hnormK → S.regs 2 = BitVec.ofNat 64 i →
      S.regs 1 = BitVec.ofNat 64 p → S.sp = s.sp - 176#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 184#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibSqr.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h4 hsp h28 h29 h18 hm hv
    janus_run [hm, hr1, hr2, hr3, hb]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h4 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, hr1, hr2, hr3, hb, key] until [hnormK]
    · -- `z[i] = 0`: one more step down
      have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ hi hv (Or.inr ?_)⟩
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

end FvModexp.Arm64.NatSqr
