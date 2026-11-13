import FvModexp.Proofs.Amd64.NatQ.DrsNorm

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the inlined `norm()` loops of the loop body (nat.go:51)

Twins of `norm1`/`norm2` (DrsNorm.lean) for `qhat = qhat.norm()` (natdiv.go:828; length `RBX`, word `RDX`,
pointer `RAX`) and the two `uu.norm()` of the correction (`norm4`, `norm5`; length `R12`, word `R9`, pointer `RDI`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

/-- `qhat.norm()`'s head (`TESTQ BX, BX`) and exit (`MOVQ 0xa8(SP), DX`) -/
abbrev nHead3 : Nat := 0x5efc4a
abbrev nExit3 : Nat := 0x5efc59

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `qhat = qhat.norm()` (natdiv.go:828): pointer `RAX`, length `RBX`, scratch `RDX` -/
theorem norm3 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExit3 → s'.mem = M →
      s'.regs 3 = BitVec.ofNat 64 n' → Same2 3 2 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 0 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHead3 → S.regs 3 = BitVec.ofNat 64 i →
      Same2 3 2 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExit3]
    refine hfin _ 0 rfl rfl ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus64_simp
    · refine ⟨fun k h1 h2 => ?_, ?_, ?_, ?_⟩
      · rw [← hS.1 k h1 h2]; try simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
      all_goals first | exact hS.2.1 | exact hS.2.2.1 | exact hS.2.2.2
  | succ i ih =>
    intro S hi hpc hl hS hm hv
    have h6 : S.regs 0 = BitVec.ofNat 64 p := by rw [hS.1 0 (by decide) (by decide)]; exact hp6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHead3, nExit3]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

/-- `uu.norm()` of the correction loop's compare (natdiv.go:833): head `TESTQ R12, R12`, exit `MOVQ 0x70(SP), R8` -/
abbrev nHead4 : Nat := 0x5efdc7
abbrev nExit4 : Nat := 0x5efdd6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `uu.norm()` (natdiv.go:833): pointer `RDI`, length `R12`, scratch `R9` -/
theorem norm4 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExit4 → s'.mem = M →
      s'.regs 12 = BitVec.ofNat 64 n' → Same2 12 9 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 7 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHead4 → S.regs 12 = BitVec.ofNat 64 i →
      Same2 12 9 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExit4]
    refine hfin _ 0 rfl rfl ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus64_simp
    · refine ⟨fun k h1 h2 => ?_, ?_, ?_, ?_⟩
      · rw [← hS.1 k h1 h2]; try simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
      all_goals first | exact hS.2.1 | exact hS.2.2.1 | exact hS.2.2.2
  | succ i ih =>
    intro S hi hpc hl hS hm hv
    have h6 : S.regs 7 = BitVec.ofNat 64 p := by rw [hS.1 7 (by decide) (by decide)]; exact hp6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHead4, nExit4]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

/-- `uu.norm()` after the correction loop (natdiv.go:844): head `TESTQ R12, R12`, exit `MOVQ 0x70(SP), R8` -/
abbrev nHead5 : Nat := 0x5eff45
abbrev nExit5 : Nat := 0x5eff54

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `uu.norm()` (natdiv.go:844): pointer `RDI`, length `R12`, scratch `R9` -/
theorem norm5 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExit5 → s'.mem = M →
      s'.regs 12 = BitVec.ofNat 64 n' → Same2 12 9 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 7 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHead5 → S.regs 12 = BitVec.ofNat 64 i →
      Same2 12 9 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExit5]
    refine hfin _ 0 rfl rfl ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus64_simp
    · refine ⟨fun k h1 h2 => ?_, ?_, ?_, ?_⟩
      · rw [← hS.1 k h1 h2]; try simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
      all_goals first | exact hS.2.1 | exact hS.2.2.1 | exact hS.2.2.2
  | succ i ih =>
    intro S hi hpc hl hS hm hv
    have h6 : S.regs 7 = BitVec.ofNat 64 p := by rw [hS.1 7 (by decide) (by decide)]; exact hp6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHead5, nExit5]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

end FvModexp.Amd64.Q.DivRec
