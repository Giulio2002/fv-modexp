import FvModexp.Proofs.Arm64.Nat.LibSqr
import FvModexp.Proofs.Common.Conv

/-!
# [Q-form copy of Arm64/Nat/KSqrLoop.lean — TIGHT COSTS, divmc s34] `karatsubaSqr` (arm64): the two inlined `norm` loops of the prologue (natmul.go:282-283, `x0 := x[:n2].norm()`,
`x1 := x[n2:].norm()`)

`for i > 0 && x[i-1] == 0 { i-- }`: loop 1 (head `0x1bc324`, `R8 = i`, base `R4`, scratch `R10`/`R11`, back edge
`0x1bc320`, exit `0x1bc338`), loop 2 (head `0x1bc35c`, `R5 = i`, base `R11`, scratch `R12`/`R13`, back edge
`0x1bc358`, exit `0x1bc370`). Continuation form: the exit gets the normalised length; every other register (`G`), the
stack pointer and the memory are unchanged.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

abbrev kL1 : Nat := 0x1bc324
abbrev kL1x : Nat := 0x1bc338
abbrev kL2 : Nat := 0x1bc35c
abbrev kL2x : Nat := 0x1bc370

theorem natVal_drop0 {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kLoop1 (impl : List Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (sp0 : BitVec 64) (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (h4 : G 4 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.pc = BitVec.ofNat 64 kL1x → S'.regs 8 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 8 → r ≠ 10 → r ≠ 11 → S'.regs r = G r) → S'.sp = sp0 → S'.mem = M → i ≤ n0 →
      natVal M xp i = V → NatNorm M xp i → ReachesRet (LibSqr.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 kL1 → S.regs 8 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 8 → r ≠ 10 → r ≠ 11 → S.regs r = G r) → S.sp = sp0 → S.mem = M → natVal M xp i = V →
      ReachesRet (LibSqr.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h8 hR hsp hm hv
    janus_run [hm] until [kL1x]
    exact hfin _ 0 rfl (by janus_simp) (fun r h1 h2 h3 => by simp [h1, h2, h3, hR]) (by janus_simp) rfl
      (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc h8 hR hsp hm hv
    have r4 : S.regs 4 = BitVec.ofNat 64 xp := (hR 4 (by decide) (by decide) (by decide)).trans h4
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key, r4] until [kL1, kL1x]
    · have hz : M.readLE (xp + 8 * i) 8 = 0 := by rw [show xp + 8 * i = xp + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl ((natVal_drop0 hz).symm.trans hv)
    · have hz : ¬M.readLE (xp + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl hi hv (Or.inr ?_)
      rw [show xp + 8 * (i + 1 - 1) = xp + i * 8 by omega]; exact hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kLoop2 (impl : List Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (sp0 : BitVec 64) (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (h11 : G 11 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.pc = BitVec.ofNat 64 kL2x → S'.regs 5 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 5 → r ≠ 12 → r ≠ 13 → S'.regs r = G r) → S'.sp = sp0 → S'.mem = M → i ≤ n0 →
      natVal M xp i = V → NatNorm M xp i → ReachesRet (LibSqr.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 kL2 → S.regs 5 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 5 → r ≠ 12 → r ≠ 13 → S.regs r = G r) → S.sp = sp0 → S.mem = M → natVal M xp i = V →
      ReachesRet (LibSqr.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h5 hR hsp hm hv
    janus_run [hm] until [kL2x]
    exact hfin _ 0 rfl (by janus_simp) (fun r h1 h2 h3 => by simp [h1, h2, h3, hR]) (by janus_simp) rfl
      (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc h5 hR hsp hm hv
    have r11 : S.regs 11 = BitVec.ofNat 64 xp := (hR 11 (by decide) (by decide) (by decide)).trans h11
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key, r11] until [kL2, kL2x]
    · have hz : M.readLE (xp + 8 * i) 8 = 0 := by rw [show xp + 8 * i = xp + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl ((natVal_drop0 hz).symm.trans hv)
    · have hz : ¬M.readLE (xp + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl hi hv (Or.inr ?_)
      rw [show xp + 8 * (i + 1 - 1) = xp + i * 8 by omega]; exact hz

end FvModexp.Arm64.Q.NatSqr
