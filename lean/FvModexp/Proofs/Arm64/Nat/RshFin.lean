import FvModexp.Proofs.Arm64.Nat.RshDefs
import FvModexp.Proofs.Arm64.Nat.LshFin

/-!
# `nat.rsh` (arm64): the inlined `z.norm()` loop (`+0x260`, `CMP $0, R1`; loop-back entry `+0x25c MOVD R3, R1`),
the return (`CMP R2, R1; BHI panic`; `MOVD -8(RSP), R29; MOVD.P 144(RSP), R30; RET`), and `fromNorm` (the post).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

abbrev hNorm : Nat := segAddr Extracted.program fn + 0x260
abbrev hJoin : Nat := segAddr Extracted.program fn + 0x1ac

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 144) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat)
    (hal : s.sp.toNat % 16 = 0) (hsp0 : 4240 ≤ s.sp.toNat) (hsp1 : s.sp.toNat + 64 ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 4240) (4240 + 64) true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hNorm → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 2 = BitVec.ofNat 64 c → S.sp = s.sp - 144#64 →
      S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 152#64 → S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibRsh.program.link impl) (s.regs 30) S fun s' =>
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
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp)
        (by janus_simp) rfl ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      all_goals try janus_simp
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

/-- the slice-pointer mask of `x[m-n:]` (`q = m - n < cap x`) -/
theorem xmask (xl xc q : Nat) (hq : q < xl) (hx : xl ≤ xc) (hc : xc < 2 ^ 40) :
    (BitVec.ofNat 64 xl - BitVec.ofNat 64 (xl - q) &&&
      (BitVec.ofNat 64 xl - (BitVec.ofNat 64 xc + BitVec.ofNat 64 (xl - q))).sshiftRight 63) = BitVec.ofNat 64 q := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitArith.asr63_toNat]
  have e1 : (BitVec.ofNat 64 xl - (BitVec.ofNat 64 xc + BitVec.ofNat 64 (xl - q))).toNat = 2 ^ 64 - (xc - q) := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 xl - BitVec.ofNat 64 (xl - q)).toNat = q := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e1, e2, if_neg (by omega), Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]

theorem sub_add_sub (xl n : Nat) (h : n ≤ xl) (hx : xl < 2 ^ 64) :
    BitVec.ofNat 64 xl + BitVec.ofNat 64 n - BitVec.ofNat 64 xl = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- the top `n` limbs of a `q + n`-limb value -/
theorem val_hi (m : Memory) (x q n : Nat) : natVal m (x + 8 * q) n = natVal m x (q + n) / 2 ^ (64 * q) := by
  rw [natVal_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (natVal_lt _ _ _), Nat.zero_add]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the norm head (memory `M2`, `z[0:n]` = `X / 2^s`) to the return, with the postcondition -/
theorem fromNorm (impl : List Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (M2 : Memory) (hF1 : MemFrame M M2 (R.rt ++ ws s p c)) (hLF1 : LiveFrame M M2 L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 28).toNat (view R.rt L' M2))
    (hval : natVal M2 p (need xl sh) = natVal s.mem x xl / 2 ^ sh)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hNorm) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M2) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48; have hpw := h.pw
  unfold Apart at hpw
  have hws : ∀ a n, (s.sp.toNat - 152 ≤ a ∧ a + n ≤ s.sp.toNat - 136) → Outside a n (R.rt ++ ws s p c) := by
    intro a n ha
    simp only [ws, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h.wrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
  refine norm impl s M2 p c (need xl sh) (natVal s.mem x xl / 2 ^ sh) _ ?_ hcap (by omega) (by omega)
    (by rw [hF1.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ h.pacc (Nat.le_refl _)
      (by omega)))
    (by rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.lr) (by rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.fp)
    h.al h.sp0 h.sp1 (by rw [hF1.accessible]; exact h.sacc) h.lr4 h.lr48 _ S (Nat.le_refl _) hpc h1 h0 h2 hsp h28
    h29 h18 hm hval
  intro s' n' hm' h0' h1' h2' hn' hv' hN
  exact h.post hF1 hLF1 hinv2 s' n' hm' h0' h1' h2' (by omega) hv' hN

end FvModexp.Arm64.Rsh
