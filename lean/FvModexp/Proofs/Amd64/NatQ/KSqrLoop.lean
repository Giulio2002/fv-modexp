import FvModexp.Proofs.Amd64.Nat.LibSqr
import FvModexp.Proofs.Common.Conv

/-!
# [amd64 port (divmc s38) of the Q-form Arm64/NatQ/KSqrLoop.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the two inlined
`norm` loops of the prologue (natmul.go:282-283, `x0 := x[:n2].norm()`, `x1 := x[n2:].norm()`)

`for i > 0 && x[i-1] == 0 { i-- }`: loop 1 (head `0x5f23f8`, `DX = i`, base `SI`, scratch `R12`, back edge `0x5f23f5`,
exit `0x5f2407`), loop 2 (head `0x5f2440`, `R8 = i`, base `R9`, scratch `R11` — reloaded from `0x48(SP')` (`8·n2`) on
both continuing paths, back edge `0x5f2437`, exit `0x5f2454`). Continuation form: the exit gets the normalised length;
every other register (`G`), the memory, `fsBase`, `DF` and `X15` are unchanged.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

abbrev kL1 : Nat := 0x5f23f8
abbrev kL1x : Nat := 0x5f2407
abbrev kL2 : Nat := 0x5f2440
abbrev kL2x : Nat := 0x5f2454

theorem natVal_drop0 {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kLoop1 (impl : List Amd64.Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (fs0 : BitVec 64) (df0 : Bool) (x0 : BitVec 128)
    (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (h6 : G 6 = BitVec.ofNat 64 xp)
    (hfin : ∀ (S' : State) (i : Nat), S'.rip = BitVec.ofNat 64 kL1x → S'.regs 2 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 2 → r ≠ 12 → S'.regs r = G r) → S'.fsBase = fs0 → S'.df = df0 → S'.xmm 15 = x0 → S'.mem = M →
      i ≤ n0 → natVal M xp i = V → NatNorm M xp i → ReachesRet (LibSqr.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 kL1 → S.regs 2 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 2 → r ≠ 12 → S.regs r = G r) → S.fsBase = fs0 → S.df = df0 → S.xmm 15 = x0 → S.mem = M →
      natVal M xp i = V → ReachesRet (LibSqr.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h2 hR hfs hdf hx hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [kL1x]
    exact hfin _ 0 rfl (by janus64_simp) (fun r h1 h2 => by simp [h1, h2, hR]) (by janus64_simp <;> exact hfs)
      (by janus64_simp <;> exact hdf) (by janus64_simp <;> exact hx) rfl (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc h2 hR hfs hdf hx hm hv
    have r6 : S.regs 6 = BitVec.ofNat 64 xp := (hR 6 (by decide) (by decide)).trans h6
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, r6, BitVec.msb_eq_decide] until [kL1, kL1x]
    all_goals first
      | (have hz : M.readLE (xp + 8 * i) 8 = 0 := by
           rw [show xp + 8 * i = xp + (i + 1) * 8 - 8 by omega]; exact hbr
         exact ih _ (by omega) rfl (by janus64_simp) (fun r h1 h2 => by simp [setRegF, h1, h2, hR])
           (by janus64_simp <;> exact hfs) (by janus64_simp <;> exact hdf) (by janus64_simp <;> exact hx) rfl
           ((natVal_drop0 hz).symm.trans hv))
      | (have hz : ¬M.readLE (xp + 8 * (i + 1 - 1)) 8 = 0 := by
           rw [show xp + 8 * (i + 1 - 1) = xp + (i + 1) * 8 - 8 by omega]; exact hbr
         exact hfin _ (i + 1) rfl (by janus64_simp) (fun r h1 h2 => by simp [setRegF, h1, h2, hR])
           (by janus64_simp <;> exact hfs) (by janus64_simp <;> exact hdf) (by janus64_simp <;> exact hx) rfl hi hv
           (Or.inr hz))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kLoop2 (impl : List Amd64.Segment) (ret : BitVec 64) (Q : State → Prop) (M : Memory) (G : Nat → BitVec 64)
    (fs0 : BitVec 64) (df0 : Bool) (x0 : BitVec 128)
    (xp n0 V : Nat) (hacc : M.accessible xp (8 * n0) false = true) (hp : xp + 8 * n0 ≤ 2 ^ 48)
    (hn0 : n0 < 2 ^ 40) (h9 : G 9 = BitVec.ofNat 64 xp)
    (h11 : M.readLE ((G 4).toNat + 72) 8 = (G 11).toNat) (hacc11 : M.accessible ((G 4).toNat + 72) 8 false = true)
    (hsp48 : (G 4).toNat + 80 ≤ 2 ^ 48)
    (hfin : ∀ (S' : State) (i : Nat), S'.rip = BitVec.ofNat 64 kL2x → S'.regs 8 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 8 → S'.regs r = G r) → S'.fsBase = fs0 → S'.df = df0 → S'.xmm 15 = x0 → S'.mem = M →
      i ≤ n0 → natVal M xp i = V → NatNorm M xp i → ReachesRet (LibSqr.program.link impl) ret S' Q) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 kL2 → S.regs 8 = BitVec.ofNat 64 i →
      (∀ r, r ≠ 8 → S.regs r = G r) → S.fsBase = fs0 → S.df = df0 → S.xmm 15 = x0 → S.mem = M →
      natVal M xp i = V → ReachesRet (LibSqr.program.link impl) ret S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h8 hR hfs hdf hx hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [kL2x]
    exact hfin _ 0 rfl (by janus64_simp) (fun r h1 => by simp [h1, hR]) (by janus64_simp <;> exact hfs)
      (by janus64_simp <;> exact hdf) (by janus64_simp <;> exact hx) rfl (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
  | succ i ih =>
    intro S hi hpc h8 hR hfs hdf hx hm hv
    have r9 : S.regs 9 = BitVec.ofNat 64 xp := (hR 9 (by decide)).trans h9
    have r4 : S.regs 4 = G 4 := hR 4 (by decide)
    have r11 : S.regs 11 = G 11 := hR 11 (by decide)
    have m11 : M.readLE ((S.regs 4).toNat + 72) 8 = (S.regs 11).toNat := by rw [r4, r11]; exact h11
    have a11 : M.accessible ((S.regs 4).toNat + 72) 8 false = true := by rw [r4]; exact hacc11
    have b11 : (S.regs 4).toNat + 80 ≤ 2 ^ 48 := by rw [r4]; exact hsp48
    have e11 : BitVec.ofNat 64 (S.regs 11).toNat = S.regs 11 := by simp
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, r9, m11, e11, BitVec.msb_eq_decide] until [kL2, kL2x]
    all_goals first
      | (have hz : M.readLE (xp + 8 * i) 8 = 0 := by
           rw [show xp + 8 * i = xp + (i + 1) * 8 - 8 by omega]; exact hbr
         exact ih _ (by omega) rfl (by janus64_simp) (fun r h1 => by
             by_cases e : r = 11
             · subst e; simp [setRegF, r11]
             · simp [setRegF, h1, e, hR])
           (by janus64_simp <;> exact hfs) (by janus64_simp <;> exact hdf) (by janus64_simp <;> exact hx) rfl
           ((natVal_drop0 hz).symm.trans hv))
      | (have hz : ¬M.readLE (xp + 8 * (i + 1 - 1)) 8 = 0 := by
           rw [show xp + 8 * (i + 1 - 1) = xp + (i + 1) * 8 - 8 by omega]; exact hbr
         exact hfin _ (i + 1) rfl (by janus64_simp) (fun r h1 => by
             by_cases e : r = 11
             · subst e; simp [setRegF, r11]
             · simp [setRegF, h1, e, hR])
           (by janus64_simp <;> exact hfs) (by janus64_simp <;> exact hdf) (by janus64_simp <;> exact hx) rfl hi hv
           (Or.inr hz))
      | fail "G2"

end FvModexp.Amd64.Q.NatSqr
