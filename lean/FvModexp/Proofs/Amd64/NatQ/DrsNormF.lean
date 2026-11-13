import FvModexp.Proofs.Amd64.NatQ.DrsNorm

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the inlined `norm()` loops of the final block (nat.go:51)

Twins of `norm4` (DrsNorm3.lean) at the final block's addresses: `normF2` (`qhat.norm()`, natdiv.go:864), `normF3`
(`u.norm()` of the final correction loop, natdiv.go:870), `normF4` (`u.norm()` after it, natdiv.go:878), `normF5`
(`qhat.norm()` of `addTo(z, qhat.norm())`, natdiv.go:891). (`u[s:].norm()` of natdiv.go:862: `normF1`, DrsNormF1.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

/-- head / exit of normF2 -/
abbrev nHdF2 : Nat := 0x5f0249
abbrev nExF2 : Nat := 0x5f0258

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `qhat.norm()` (natdiv.go:864): pointer `RAX`, length `RBX`, scratch `RCX` -/
theorem normF2 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExF2 → s'.mem = M →
      s'.regs 3 = BitVec.ofNat 64 n' → Same2 3 1 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 0 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHdF2 → S.regs 3 = BitVec.ofNat 64 i →
      Same2 3 1 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExF2]
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
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHdF2, nExF2]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

/-- head / exit of normF3 -/
abbrev nHdF3 : Nat := 0x5f0382
abbrev nExF3 : Nat := 0x5f0391

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u.norm()` (natdiv.go:870): pointer `RDI`, length `R8`, scratch `R9` -/
theorem normF3 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExF3 → s'.mem = M →
      s'.regs 8 = BitVec.ofNat 64 n' → Same2 8 9 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 7 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHdF3 → S.regs 8 = BitVec.ofNat 64 i →
      Same2 8 9 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExF3]
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
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHdF3, nExF3]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

/-- head / exit of normF4 -/
abbrev nHdF4 : Nat := 0x5f0522
abbrev nExF4 : Nat := 0x5f0531

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u.norm()` (natdiv.go:878): pointer `RDI`, length `R8`, scratch `R9` -/
theorem normF4 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExF4 → s'.mem = M →
      s'.regs 8 = BitVec.ofNat 64 n' → Same2 8 9 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 7 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHdF4 → S.regs 8 = BitVec.ofNat 64 i →
      Same2 8 9 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExF4]
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
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHdF4, nExF4]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

/-- head / exit of normF5 -/
abbrev nHdF5 : Nat := 0x5f0645
abbrev nExF5 : Nat := 0x5f0654

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `qhat.norm()` (natdiv.go:891): pointer `RDI`, length `RBX`, scratch `RDX` -/
theorem normF5 (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExF5 → s'.mem = M →
      s'.regs 3 = BitVec.ofNat 64 n' → Same2 3 2 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp6 : S0.regs 7 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 nHdF5 → S.regs 3 = BitVec.ofNat 64 i →
      Same2 3 2 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hS hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [nExF5]
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
    janus64_run [hm, key, BitVec.msb_eq_decide] until [nHdF5, nExF5]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hbr
      refine ih _ (by omega) rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ rfl
        ((natVal_drop_zero hbr).symm.trans hv)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h1, h2, ite_false]
    · rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hbr
      refine hfin _ (i + 1) rfl rfl (by janus64_simp) ⟨fun k h1 h2 => ?_, hS.2.1, hS.2.2.1, hS.2.2.2⟩ hi hv
        (Or.inr hbr)
      rw [← hS.1 k h1 h2]; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, ite_false]

end FvModexp.Amd64.Q.DivRec
