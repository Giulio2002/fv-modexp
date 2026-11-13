import FvModexp.Proofs.Arm64.Nat.DrsDefs

/-!
# `divRecursiveStep` (arm64): the inlined `norm()` loops (natdiv.go:754/755/817/…; nat.go:51)

Each loop `for n > 0 && z[n-1] == 0 { n-- }` is `CMP $0, Rl; BLE exit; SUB $1, Rl, Ra; MOVD (Rp)(Ra<<3), Rb; CBZ Rb, back`
with `back: MOVD Ra, Rl`. From the head with length `i` it reaches the exit with the normalised length `n' ≤ i`; the
memory, `SP`, `X28/X29/X18` and every register other than `Rl, Ra, Rb` are unchanged (`Same3`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option autoImplicit false
set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- (= `drsNatVal_drop_zero`, restated here so that drs does not import the divLarge chain) -/
theorem drsNatVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

/-- every register but `a`, `b`, `c` is as in `S` -/
@[reducible] def Same3 (a b c : Nat) (S s' : State) : Prop := ∀ k, k ≠ a → k ≠ b → k ≠ c → s'.regs k = S.regs k

theorem Same3.trans {a b c : Nat} {S T U : State} (h1 : Same3 a b c S T) (h2 : Same3 a b c T U) : Same3 a b c S U :=
  fun k ha hb hc => (h2 k ha hb hc).trans (h1 k ha hb hc)

abbrev nHead1 : Nat := 0x1ba3e0
abbrev nExit1 : Nat := 0x1ba3f4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u = u.norm()` at the entry (natdiv.go:754): pointer `R4`, length `R5`, scratch `R11, R12` -/
theorem norm1 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit1 → s'.mem = M → s'.regs 5 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 5 11 12 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 4 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead1 → S.regs 5 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 5 11 12 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit1]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 4 = BitVec.ofNat 64 p := by rw [hS 4 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead1, nExit1]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead2 : Nat := 0x1ba408
abbrev nExit2 : Nat := 0x1ba41c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `v = v.norm()` at the entry (natdiv.go:755): pointer `R7`, length `R8`, scratch `R11, R12` -/
theorem norm2 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit2 → s'.mem = M → s'.regs 8 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 8 11 12 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 7 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead2 → S.regs 8 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 8 11 12 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit2]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 7 = BitVec.ofNat 64 p := by rw [hS 7 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead2, nExit2]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead3 : Nat := 0x1ba62c
abbrev nExit3 : Nat := 0x1ba640

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `qhat = qhat.norm()` in the loop: pointer `R0`, length `R1`, scratch `R3, R4` -/
theorem norm3 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit3 → s'.mem = M → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 1 3 4 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 0 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead3 → S.regs 1 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 1 3 4 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit3]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 0 = BitVec.ofNat 64 p := by rw [hS 0 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead3, nExit3]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead4 : Nat := 0x1ba71c
abbrev nExit4 : Nat := 0x1ba730

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `uu.norm()` in the correction loop: pointer `R6`, length `R19`, scratch `R7, R8` -/
theorem norm4 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit4 → s'.mem = M → s'.regs 19 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 19 7 8 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 6 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead4 → S.regs 19 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 19 7 8 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit4]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 6 = BitVec.ofNat 64 p := by rw [hS 6 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead4, nExit4]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead5 : Nat := 0x1ba820
abbrev nExit5 : Nat := 0x1ba834

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `uu.norm()` after the correction loop: pointer `R3`, length `R19`, scratch `R6, R7` -/
theorem norm5 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit5 → s'.mem = M → s'.regs 19 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 19 6 7 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 3 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead5 → S.regs 19 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 19 6 7 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit5]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 3 = BitVec.ofNat 64 p := by rw [hS 3 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead5, nExit5]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead6 : Nat := 0x1ba98c
abbrev nExit6 : Nat := 0x1ba9a0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u[s:].norm()` (final block): pointer `R4`, length `R15`, scratch `R16, R19` -/
theorem norm6 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit6 → s'.mem = M → s'.regs 15 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 15 16 19 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 4 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead6 → S.regs 15 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 15 16 19 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit6]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 4 = BitVec.ofNat 64 p := by rw [hS 4 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead6, nExit6]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead7 : Nat := 0x1baa18
abbrev nExit7 : Nat := 0x1baa2c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `qhat = qhat.norm()` (final block): pointer `R0`, length `R1`, scratch `R2, R3` -/
theorem norm7 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit7 → s'.mem = M → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 1 2 3 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 0 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead7 → S.regs 1 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 1 2 3 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit7]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 0 = BitVec.ofNat 64 p := by rw [hS 0 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead7, nExit7]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead8 : Nat := 0x1baad4
abbrev nExit8 : Nat := 0x1baae8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u.norm()` in the final correction loop: pointer `R6`, length `R5`, scratch `R7, R8` -/
theorem norm8 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit8 → s'.mem = M → s'.regs 5 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 5 7 8 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 6 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead8 → S.regs 5 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 5 7 8 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit8]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 6 = BitVec.ofNat 64 p := by rw [hS 6 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead8, nExit8]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead9 : Nat := 0x1babe4
abbrev nExit9 : Nat := 0x1babf8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u.norm()` after the final correction loop: pointer `R3`, length `R5`, scratch `R6, R7` -/
theorem norm9 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit9 → s'.mem = M → s'.regs 5 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 5 6 7 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 3 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead9 → S.regs 5 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 5 6 7 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit9]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 3 = BitVec.ofNat 64 p := by rw [hS 3 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead9, nExit9]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

abbrev nHead10 : Nat := 0x1baca8
abbrev nExit10 : Nat := 0x1bacbc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `qhat.norm()` of `addTo(z, qhat.norm())`: pointer `R3`, length `R1`, scratch `R6, R7` -/
theorem norm10 (impl : List Segment) (r : W64) (M : Memory) (p n0 V : Nat) (S0 : State) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.pc = BitVec.ofNat 64 nExit10 → s'.mem = M → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.sp = S0.sp → Same3 1 6 7 S0 s' → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDrs.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hp4 : S0.regs 3 = BitVec.ofNat 64 p) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 nHead10 → S.regs 1 = BitVec.ofNat 64 i →
      S.sp = S0.sp → Same3 1 6 7 S0 S → S.mem = M → natVal M p i = V → ReachesRet (LibDrs.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hl hsp hS hm hv
    janus_run [hm] until [nExit10]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    · janus_simp
    · janus_simp
    · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
  | succ i ih =>
    intro S hi hpc hl hsp hS hm hv
    have h4 : S.regs 3 = BitVec.ofNat 64 p := by rw [hS 3 (by decide) (by decide) (by decide)]; exact hp4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key] until [nHead10, nExit10]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      refine ih _ (by omega) rfl (by janus_simp) (by janus_simp) ?_ rfl ((drsNatVal_drop_zero hz).symm.trans hv)
      intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      · janus_simp
      · janus_simp
      · intro k h1 h2 h3; rw [← hS k h1 h2 h3]; try simp only [setReg, h1, h2, h3, ite_false]
      · rw [show p + 8 * (i + 1 - 1) = p + i * 8 by omega]; exact hz

end FvModexp.Arm64.DivRec
