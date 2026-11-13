import FvModexp.Proofs.Arm64.Nat.LibMul
import FvModexp.Proofs.Common.Conv

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/KMulLoop.lean — TIGHT COSTS, divmc s34] `karatsuba` (arm64): the four inlined `norm` loops of the prologue (natmul.go:197-198, `x[:n2].norm()`,
`x[n2:].norm()`, `y[:n2].norm()`, `y[n2:].norm()`; nat.go:51)

`for i > 0 && x[i-1] == 0 { i-- }` (adapted from this repo's `KSqrLoop`): each lemma is in continuation form: the exit
gets the normalised length; every other register (`G`), the stack pointer and the memory are unchanged.
* x0: head `0x1bbf14`, `R11 = i`, base `R4`, scratch `R13`/`R14`, exit `0x1bbf28`;
* x1: head `0x1bbf4c`, `R5 = i`, base `R14`, scratch `R15`/`R16`, exit `0x1bbf60`;
* y0: head `0x1bbf94`, `R12 = i`, base `R7`, scratch `R5`/`R6`, exit `0x1bbfa8`;
* y1: head `0x1bbfcc`, `R8 = i`, base `R6`, scratch `R11`/`R13`, exit `0x1bbfe0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

theorem km_drop0 {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmLoopX0 (impl : List Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (sp0 : BitVec 64) (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (hb : G 4 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.pc = BitVec.ofNat 64 0x1bbf28 → S'.regs 11 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 11 → r ≠ 13 → r ≠ 14 → S'.regs r = G r) → S'.sp = sp0 → S'.mem = M → i ≤ n0 →
      natVal M xp i = V → NatNorm M xp i → ReachesRet (LibMul.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 0x1bbf14 → S.regs 11 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 11 → r ≠ 13 → r ≠ 14 → S.regs r = G r) → S.sp = sp0 → S.mem = M → natVal M xp i = V →
      ReachesRet (LibMul.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hR hsp hm hv
    janus_run [hm] until [0x1bbf28]
    exact hfin _ 0 rfl (by janus_simp) (fun r h1 h2 h3 => by simp [h1, h2, h3, hR]) (by janus_simp) rfl
      (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc hi0 hR hsp hm hv
    have rb : S.regs 4 = BitVec.ofNat 64 xp := (hR 4 (by decide) (by decide) (by decide)).trans hb
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key, rb] until [0x1bbf14, 0x1bbf28]
    · have hz : M.readLE (xp + 8 * i) 8 = 0 := by rw [show xp + 8 * i = xp + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl ((km_drop0 hz).symm.trans hv)
    · have hz : ¬M.readLE (xp + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl hi hv (Or.inr ?_)
      rw [show xp + 8 * (i + 1 - 1) = xp + i * 8 by omega]; exact hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmLoopX1 (impl : List Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (sp0 : BitVec 64) (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (hb : G 14 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.pc = BitVec.ofNat 64 0x1bbf60 → S'.regs 5 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 5 → r ≠ 15 → r ≠ 16 → S'.regs r = G r) → S'.sp = sp0 → S'.mem = M → i ≤ n0 →
      natVal M xp i = V → NatNorm M xp i → ReachesRet (LibMul.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 0x1bbf4c → S.regs 5 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 5 → r ≠ 15 → r ≠ 16 → S.regs r = G r) → S.sp = sp0 → S.mem = M → natVal M xp i = V →
      ReachesRet (LibMul.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hR hsp hm hv
    janus_run [hm] until [0x1bbf60]
    exact hfin _ 0 rfl (by janus_simp) (fun r h1 h2 h3 => by simp [h1, h2, h3, hR]) (by janus_simp) rfl
      (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc hi0 hR hsp hm hv
    have rb : S.regs 14 = BitVec.ofNat 64 xp := (hR 14 (by decide) (by decide) (by decide)).trans hb
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key, rb] until [0x1bbf4c, 0x1bbf60]
    · have hz : M.readLE (xp + 8 * i) 8 = 0 := by rw [show xp + 8 * i = xp + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl ((km_drop0 hz).symm.trans hv)
    · have hz : ¬M.readLE (xp + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl hi hv (Or.inr ?_)
      rw [show xp + 8 * (i + 1 - 1) = xp + i * 8 by omega]; exact hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmLoopY0 (impl : List Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (sp0 : BitVec 64) (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (hb : G 7 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.pc = BitVec.ofNat 64 0x1bbfa8 → S'.regs 12 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 12 → r ≠ 5 → r ≠ 6 → S'.regs r = G r) → S'.sp = sp0 → S'.mem = M → i ≤ n0 →
      natVal M xp i = V → NatNorm M xp i → ReachesRet (LibMul.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 0x1bbf94 → S.regs 12 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 12 → r ≠ 5 → r ≠ 6 → S.regs r = G r) → S.sp = sp0 → S.mem = M → natVal M xp i = V →
      ReachesRet (LibMul.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hR hsp hm hv
    janus_run [hm] until [0x1bbfa8]
    exact hfin _ 0 rfl (by janus_simp) (fun r h1 h2 h3 => by simp [h1, h2, h3, hR]) (by janus_simp) rfl
      (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc hi0 hR hsp hm hv
    have rb : S.regs 7 = BitVec.ofNat 64 xp := (hR 7 (by decide) (by decide) (by decide)).trans hb
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key, rb] until [0x1bbf94, 0x1bbfa8]
    · have hz : M.readLE (xp + 8 * i) 8 = 0 := by rw [show xp + 8 * i = xp + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl ((km_drop0 hz).symm.trans hv)
    · have hz : ¬M.readLE (xp + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl hi hv (Or.inr ?_)
      rw [show xp + 8 * (i + 1 - 1) = xp + i * 8 by omega]; exact hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmLoopY1 (impl : List Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (sp0 : BitVec 64) (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (hb : G 6 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.pc = BitVec.ofNat 64 0x1bbfe0 → S'.regs 8 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 8 → r ≠ 11 → r ≠ 13 → S'.regs r = G r) → S'.sp = sp0 → S'.mem = M → i ≤ n0 →
      natVal M xp i = V → NatNorm M xp i → ReachesRet (LibMul.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 0x1bbfcc → S.regs 8 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 8 → r ≠ 11 → r ≠ 13 → S.regs r = G r) → S.sp = sp0 → S.mem = M → natVal M xp i = V →
      ReachesRet (LibMul.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hR hsp hm hv
    janus_run [hm] until [0x1bbfe0]
    exact hfin _ 0 rfl (by janus_simp) (fun r h1 h2 h3 => by simp [h1, h2, h3, hR]) (by janus_simp) rfl
      (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc hi0 hR hsp hm hv
    have rb : S.regs 6 = BitVec.ofNat 64 xp := (hR 6 (by decide) (by decide) (by decide)).trans hb
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hm, key, rb] until [0x1bbfcc, 0x1bbfe0]
    · have hz : M.readLE (xp + 8 * i) 8 = 0 := by rw [show xp + 8 * i = xp + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl ((km_drop0 hz).symm.trans hv)
    · have hz : ¬M.readLE (xp + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl (by janus_simp) (fun r h1 h2 h3 => by simp [setReg, h1, h2, h3, hR]) (by janus_simp)
        rfl hi hv (Or.inr ?_)
      rw [show xp + 8 * (i + 1 - 1) = xp + i * 8 by omega]; exact hz

end FvModexp.Arm64.Q.NatMul
