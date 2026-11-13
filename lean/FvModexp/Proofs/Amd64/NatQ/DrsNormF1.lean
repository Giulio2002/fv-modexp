import FvModexp.Proofs.Amd64.NatQ.DrsNorm

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the inlined `u[s:].norm()` of the final block (natdiv.go:862, nat.go:51)

Pointer `R13`, length `R12`, scratch `R10` (reloaded from `0x60(SP)` on both paths); head `TESTQ R12, R12`
(`0x5f016a`), exit `CMPQ R12, DI` (`0x5f0180`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

abbrev nHdF1 : Nat := 0x5f016a
abbrev nExF1 : Nat := 0x5f0180

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u[s:].norm()` (natdiv.go:862): pointer `R13`, length `R12`, scratch `R10` (reloaded from `0x60(SP)`) -/
theorem normF1 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExF1 → s'.mem = M →
      s'.regs 12 = BitVec.ofNat 64 n' → Same2 12 10 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 13 = BitVec.ofNat 64 p) (a : Nat) (hsp0 : S0.regs 4 = BitVec.ofNat 64 a)
    (ha : a + 0x68 ≤ 2 ^ 48) (hacc4 : M.accessible (a + 0x60) 8 false = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHdF1 → S.regs 12 = BitVec.ofNat 64 i →
      Same2 12 10 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    have h4 : S.regs 4 = BitVec.ofNat 64 a := by rw [hS.1 4 (by decide) (by decide)]; exact hsp0
    janus64_run [hm, BitVec.msb_eq_decide] until [nExF1]
    refine hfin _ 0 rfl rfl ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus64_simp
    · refine ⟨fun k h1 h2 => ?_, ?_, ?_, ?_⟩
      · rw [← hS.1 k h1 h2]; try simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
      all_goals first | exact hS.2.1 | exact hS.2.2.1 | exact hS.2.2.2
  | succ i ih =>
    intro S hi hpc hl hS hm hv
    have h4 : S.regs 4 = BitVec.ofNat 64 a := by rw [hS.1 4 (by decide) (by decide)]; exact hsp0
    have h6 : S.regs 13 = BitVec.ofNat 64 p := by rw [hS.1 13 (by decide) (by decide)]; exact hp6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHdF1, nExF1]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

end FvModexp.Amd64.Q.DivRec
