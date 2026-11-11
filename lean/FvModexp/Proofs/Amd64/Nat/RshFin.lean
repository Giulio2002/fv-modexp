import FvModexp.Proofs.Amd64.Nat.RshDefs
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.rsh` (amd64): the inlined `z.norm()` loop (`+0x2e0`, `TESTQ DI, DI`; loop-back `+0x2da DECQ DI`), the return
(`CMPQ DI, CX; JA panic; MOVQ DI, BX; ADDQ $0x88, SP; POPQ BP; RET`), and `fromNorm` (the post).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (natVal_drop_zero)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Amd64.Segment) (s : State) (M : Janus.Arm64.Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c → s'.fsBase = s.fsBase → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 4248 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 64 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hNorm → S.regs 7 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 1 = BitVec.ofNat 64 c → S.regs 4 = s.regs 4 - 144#64 →
      S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase →
      S.df = false → S.mem = M → natVal M p i = V →
      ReachesRet (LibRsh.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Q s' := by
  have hcm : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  intro i
  induction i with
  | zero =>
    intro S hi hpc h2 h0 h1 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hcm, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfin _ 0 rfl ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hx15 | exact hdf | omega
  | succ i ih =>
    intro S hi hpc h2 h0 h1 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hcm, key, BitVec.msb_eq_decide] until [hNorm]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by first | (janus64_simp; done) | (janus64_simp; exact hx15)) (by first | (janus64_simp; done) | (janus64_simp; exact hfs))
        (by first | exact hdf | (janus64_simp; done) | (janus64_simp; exact hdf)) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfin _ (i + 1) rfl ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hx15 | exact hdf | omega

/-- the top `n` limbs of a `q + n`-limb value -/
theorem val_hi (m : Janus.Arm64.Memory) (x q n : Nat) :
    natVal m (x + 8 * q) n = natVal m x (q + n) / 2 ^ (64 * q) := by
  rw [natVal_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (natVal_lt _ _ _), Nat.zero_add]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the norm head (memory `M2`, `z[0:n]` = `X / 2^s`) to the return, with the postcondition -/
theorem fromNorm (impl : List Amd64.Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (M2 : Janus.Arm64.Memory) (hF1 : MemFrame M M2 (R.rt ++ ws s p c)) (hLF1 : LiveFrame M M2 L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' M2))
    (hval : natVal M2 p (need xl sh) = natVal s.mem x xl / 2 ^ sh)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hNorm) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h7 : S.regs 7 = BitVec.ofNat 64 (need xl sh)) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M2) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48; have hpw := h.pw
  unfold Apart at hpw
  have hws : ∀ a n, ((s.regs 4).toNat - 8 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 8) → Outside a n (R.rt ++ ws s p c) := by
    intro a n ha
    simp only [ws, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h.wrt.of_sub (by omega) (by omega), by omega, by omega⟩
  refine norm impl s M2 p c (need xl sh) (natVal s.mem x xl / 2 ^ sh) _ ?_ hcap (by omega) (by omega)
    (by
      rw [hF1.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)))
    (by rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.lr) (by rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.fp)
    h.al h.sp0 h.sp1 (by rw [hF1.accessible]; exact h.sacc) h.ra47 _ S (Nat.le_refl _) hpc h7 h0 h1 hsp h14 h5 hx15
    hfs hdf hm hval
  intro s' n' hm' h0' h1' h2' hfs' hn' hv' hN
  exact h.post hF1 hLF1 hinv2 s' n' hm' h0' h1' h2' hfs' (by omega) hv' hN

end FvModexp.Amd64.Rsh
