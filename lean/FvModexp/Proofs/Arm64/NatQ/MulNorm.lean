import FvModexp.Proofs.Arm64.NatQ.MulRel
import FvModexp.Proofs.Arm64.NatQ.SqrNorm

/-!
# [Q-form copy of Arm64/Nat/MulNorm.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64): the two inlined `z.norm()` loops

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]`; the result is stored to `152..175(SP')` (`SP' = SP - 256`).
`normA` (after `basicMul`, head `0x1bb178`: `R0 = p`, `R1 = i`, cap from `96(SP')`) returns; `normB` (after
`karatsuba` / the chunk loop, head `0x1bb28c`: `R3 = p`, `R1 = i`, `R0` = the defer bits) stops at `0x1bb2b4` (the
deferred-call tests); `retB0`: from there with no deferred call, the return.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (natVal_drop_zero)

abbrev hnormA : Nat := 0x1bb178

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normA (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [(s.sp.toNat - 104, s.sp.toNat - 80)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' → s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 →
      natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (hr3 : M.readLE (s.sp.toNat - 160) 8 = c) (hal : s.sp.toNat % 16 = 0) (hsp0 : 264 ≤ s.sp.toNat)
    (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 264) 264 true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hnormA → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.sp = s.sp - 256#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 264#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ Q s' := by
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
    janus_run [hm, hr1, hr2, hr3, key] until [hnormA]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ hi hv (Or.inr ?_)⟩
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

abbrev hnormB : Nat := 0x1bb28c

/-- the state at the deferred-call tests `0x1bb2b4` after `normB` -/
structure AtB (s S : State) (M : Memory) (p c n' bits : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 0x1bb2b4
  r0 : S.regs 0 = BitVec.ofNat 64 bits
  sp : S.sp = s.sp - 256#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 264#64
  x18 : S.regs 18 = s.regs 18
  fr : MemFrame M S.mem [(s.sp.toNat - 104, s.sp.toNat - 80)]
  m152 : S.mem.readLE (s.sp.toNat - 104) 8 = p
  m160 : S.mem.readLE (s.sp.toNat - 96) 8 = n'
  m168 : S.mem.readLE (s.sp.toNat - 88) 8 = c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normB (impl : List Segment) (s : State) (M : Memory) (p c n0 V bits : Nat) (Q : State → Prop)
    (hfin : ∀ (S' : State) (n' : Nat), AtB s S' M p c n' bits → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibMul.program.link impl) (s.regs 30) S' Q)
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr3 : M.readLE (s.sp.toNat - 160) 8 = c) (hbits : bits < 256) (hal : s.sp.toNat % 16 = 0)
    (hsp0 : 264 ≤ s.sp.toNat) (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 264) 264 true = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hnormB → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 3 = BitVec.ofNat 64 p → S.regs 0 = BitVec.ofNat 64 bits → S.sp = s.sp - 256#64 →
      S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 264#64 →
      S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibMul.program.link impl) (s.regs 30) S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h4 h0 hsp h28 h29 h18 hm hv
    janus_run [hm, hr3] until [0x1bb2b4]
    refine hfin _ 0 ⟨?_, ?_, ?_, ?_, ?_, ?_, by janus_frame, ?_, ?_, ?_⟩ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h4 h0 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, hr3, key] until [hnormB, 0x1bb2b4]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
        (by janus_simp) (by janus_simp) rfl ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) ⟨?_, ?_, ?_, ?_, ?_, ?_, by janus_frame, ?_, ?_, ?_⟩ hi hv (Or.inr ?_)
      all_goals try janus_simp
      all_goals try omega
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- no deferred call (`bits = 0`): reload the result and return -/
theorem retB0 (impl : List Segment) (s S : State) (M : Memory) (p c n' : Nat) (hB : AtB s S M p c n' 0)
    (hr1 : M.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat)
    (hal : s.sp.toNat % 16 = 0) (hsp0 : 264 ≤ s.sp.toNat) (hsp1 : s.sp.toNat ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 264) 264 true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) (hp : p < 2 ^ 64) (hn : n' < 2 ^ 64) (hc : c < 2 ^ 64) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ s'.mem = S.mem ∧
      s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 n' ∧ s'.regs 2 = BitVec.ofNat 64 c := by
  obtain ⟨hpc, h0, hsp, h28, h29, h18, hF, m1, m2, m3⟩ := hB
  have e1 : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat := by
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hr1
  have e2 : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat := by
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hr2
  have ea : S.mem.accessible (s.sp.toNat - 264) 264 true = true := by rw [hF.accessible]; exact hsacc
  clear hF
  janus_run [e1, e2, m1, m2, m3]
  all_goals try janus_simp
  all_goals (refine ⟨?_, ?_, ?_, ?_⟩ <;> janus_simp)

end FvModexp.Arm64.Q.NatMul
