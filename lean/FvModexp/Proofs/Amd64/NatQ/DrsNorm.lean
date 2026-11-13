import FvModexp.Proofs.Amd64.NatQ.DrsDefs

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the inlined `norm()` loops at the entry (natdiv.go:754/755; nat.go:51)

Each loop `for n > 0 && z[n-1] == 0 { n-- }` is `TESTQ Rl, Rl; JLE exit; MOVQ -8(Rp)(Rl*8), Rb; TESTQ Rb, Rb; JE back`
with `back: DECQ Rl` falling into the head. From the head with length `i` it reaches the exit with the normalised
length `n' ≤ i`; memory, `fsBase`, `DF`, `X15` and every register other than `Rl, Rb` are unchanged (`Same2`).
Twin of Arm64/Nat/DrsNorm.lean (`norm1`, `norm2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

/-- every register but `a`, `b` is as in `S`; `fsBase`, `DF`, `X15` kept -/
@[reducible] def Same2 (a b : Nat) (S s' : State) : Prop :=
  (∀ k, k ≠ a → k ≠ b → s'.regs k = S.regs k) ∧ s'.fsBase = S.fsBase ∧ s'.df = S.df ∧ s'.xmm 15 = S.xmm 15

theorem Same2.trans {a b : Nat} {S T U : State} (h1 : Same2 a b S T) (h2 : Same2 a b T U) : Same2 a b S U :=
  ⟨fun k ha hb => (h2.1 k ha hb).trans (h1.1 k ha hb), h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.trans h1.2.2.2⟩

/-- `u.norm()`'s head (`TESTQ R8, R8`) and exit (`CMPQ R9, R8`) -/
abbrev nHead1 : Nat := 0x5ef8c2
abbrev nExit1 : Nat := 0x5ef8d1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u = u.norm()` at the entry (natdiv.go:754): pointer `RSI`, length `R8`, scratch `RDX` -/
theorem norm1 (impl : List Amd64.Segment) (r : Nat) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExit1 → s'.mem = M →
      s'.regs 8 = BitVec.ofNat 64 n' → Same2 8 2 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 6 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHead1 → S.regs 8 = BitVec.ofNat 64 i →
      Same2 8 2 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExit1]
    refine hfin _ 0 rfl rfl ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus64_simp
    · refine ⟨fun k h1 h2 => ?_, ?_, ?_, ?_⟩
      · rw [← hS.1 k h1 h2]; try simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
      all_goals first | exact hS.2.1 | exact hS.2.2.1 | exact hS.2.2.2
  | succ i ih =>
    intro S hi hpc hl hS hm hv
    have h6 : S.regs 6 = BitVec.ofNat 64 p := by rw [hS.1 6 (by decide) (by decide)]; exact hp6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHead1, nExit1]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

/-- `v.norm()`'s head (`TESTQ R11, R11`) and exit (`MOVQ 0x1a0(SP), R12`) -/
abbrev nHead2 : Nat := 0x5ef8f0
abbrev nExit2 : Nat := 0x5ef8ff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `v = v.norm()` at the entry (natdiv.go:755): pointer `RDX`, length `R11`, scratch `R12` -/
theorem norm2 (impl : List Amd64.Segment) (r : Nat) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExit2 → s'.mem = M →
      s'.regs 11 = BitVec.ofNat 64 n' → Same2 11 12 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 2 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHead2 → S.regs 11 = BitVec.ofNat 64 i →
      Same2 11 12 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExit2]
    refine hfin _ 0 rfl rfl ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus64_simp
    · refine ⟨fun k h1 h2 => ?_, ?_, ?_, ?_⟩
      · rw [← hS.1 k h1 h2]; try simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
      all_goals first | exact hS.2.1 | exact hS.2.2.1 | exact hS.2.2.2
  | succ i ih =>
    intro S hi hpc hl hS hm hv
    have h6 : S.regs 2 = BitVec.ofNat 64 p := by rw [hS.1 2 (by decide) (by decide)]; exact hp6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHead2, nExit2]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

end FvModexp.Amd64.Q.DivRec
