import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Common.ExpPow2

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `n := m.trailingZeroBits()` (nat.go:364-374, inlined; asm s55, twin of infra's arm64 EvTz)

The loop at `tzH = fnE + 0x598` (`CMPQ DX, BX; JBE panicBounds; MOVQ (R10)(BX*8), R11; TESTQ R11, R11; JE tzI;
SHLQ $6, BX; BSFQ R11, R11; ADDQ R11, BX; JMP enS`, `tzI: INCQ BX`), by induction on `ml - i`; `panicBounds` at
`i = len m` is unreachable for `0 < M`; exit `enS` with `RBX = tz M` (`Exp.tz_words`, `ctz_eq`: `BSF w = tz w` for a
non-zero word). Pure segment: memory, `RSP` and every register but `RBX`/`R11` unchanged (flags clobbered).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `BSF`'s count (`Janus.Amd64.ctzNat`) is `Exp.tz` on a value with a non-zero bit below `2^n` -/
theorem ctzNat_eq : ∀ (n x : Nat), x % 2 ^ n ≠ 0 → Janus.Amd64.ctzNat n x = Exp.tz x
  | 0, x, h => absurd (Nat.mod_one x) (by simpa using h)
  | n + 1, x, h => by
    unfold Janus.Amd64.ctzNat
    by_cases ho : x % 2 = 1
    · rw [if_pos ho, Exp.tz_odd ho]
    · rw [if_neg ho]
      have he : x % 2 = 0 := by omega
      have hx : x ≠ 0 := by intro h0; rw [h0, Nat.zero_mod] at h; exact h rfl
      have h2 : x / 2 % 2 ^ n ≠ 0 := by
        intro h0
        have : x % 2 ^ (n + 1) = 2 * (x / 2 % 2 ^ n) + x % 2 := by
          rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]; omega
        rw [this, h0, he] at h; exact h rfl
      rw [Exp.tz_even hx he, ctzNat_eq n (x / 2) h2]

theorem ctz_eq {w : Nat} (hw : w ≠ 0) (hw64 : w < 2 ^ 64) : Janus.Amd64.ctzNat 64 w = Exp.tz w :=
  ctzNat_eq 64 w (by rw [Nat.mod_eq_of_lt hw64]; exact hw)

theorem words_zero_lt {X ml : Nat} (hz : ∀ j, j < ml → Exp.wd X j = 0) (hX : X < Exp.B ^ ml) : X = 0 := by
  have := Exp.mod_B_pow_zero X ml hz; rwa [Nat.mod_eq_of_lt hX] at this

theorem tz_wd_lt {w : Nat} (hw : w ≠ 0) (hw64 : w < 2 ^ 64) : Exp.tz w < 64 := by
  have hs := (Exp.tz_spec (x := w) (by omega)).1
  have hq : 0 < w / 2 ^ Exp.tz w := by
    rcases Nat.eq_zero_or_pos (w / 2 ^ Exp.tz w) with h0 | h0
    · rw [h0, Nat.mul_zero] at hs; omega
    · exact h0
  have : 2 ^ Exp.tz w ≤ w := by
    calc 2 ^ Exp.tz w ≤ 2 ^ Exp.tz w * (w / 2 ^ Exp.tz w) := Nat.le_mul_of_pos_right _ hq
      _ = w := hs.symm
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt this hw64)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- one loop iteration from the head `tzH` (`RBX = i < ml`, word `w = [mp + 8i]`): zero word → back at `tzH` with
`RBX = i + 1`; non-zero → `enS` with `RBX = 64 i + tz w` (only `RBX`, `R11`, `RIP`, flags change) -/
theorem tzStep {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (mpB : BitVec 64) (ml i w : Nat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 tzH) (r10 : S.regs 10 = mpB) (r2 : S.regs 2 = BitVec.ofNat 64 ml)
    (r3 : S.regs 3 = BitVec.ofNat 64 i) (hil : i < ml) (h48 : mpB.toNat + 8 * ml ≤ 2 ^ 48)
    (hacc : S.mem.accessible mpB.toNat (8 * ml) false = true)
    (hrd : S.mem.readLE (mpB.toNat + i * 8) 8 = w) (hw64 : w < 2 ^ 64)
    (K0 : w = 0 → ∀ S' : State, S'.rip = BitVec.ofNat 64 tzH → S'.mem = S.mem → S'.fsBase = S.fsBase →
      S'.xmm 15 = S.xmm 15 → S'.df = S.df → (∀ r, r ≠ 3 → r ≠ 11 → S'.regs r = S.regs r) →
      S'.regs 3 = BitVec.ofNat 64 (i + 1) → ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (K1 : w ≠ 0 → ∀ S' : State, S'.rip = BitVec.ofNat 64 enS → S'.mem = S.mem → S'.fsBase = S.fsBase →
      S'.xmm 15 = S.xmm 15 → S'.df = S.df → (∀ r, r ≠ 3 → r ≠ 11 → S'.regs r = S.regs r) →
      S'.regs 3 = BitVec.ofNat 64 (64 * i + Exp.tz w) → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hml : ml < 2 ^ 46 := by omega
  have hacc' : S.mem.accessible (mpB.toNat + i * 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  by_cases hw : w = 0
  · subst hw
    janus64_run [hrd] until [tzH]
    refine K0 rfl _ rfl rfl rfl rfl rfl (fun r a b => ?_) ?_
    · janus64_simp; try simp only [if_neg a, if_neg b]
    · janus64_simp
  · have hc := ctz_eq hw hw64
    have ht := tz_wd_lt hw hw64
    janus64_run [hrd, hc] until [enS]
    refine K1 hw _ rfl rfl rfl rfl rfl (fun r a b => ?_) ?_
    · janus64_simp; try simp only [if_neg a, if_neg b]
    · janus64_simp
      apply BitVec.eq_of_toNat_eq
      have hi : i < 2 ^ 46 := by omega
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show i * 2 ^ 6 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show Exp.tz w < 2 ^ 64 by omega)]
      omega

/-- what the loop keeps: every register but `RBX`/`R11`, memory, FS base, `X15`, `DF` -/
@[reducible] def TzKeep (S0 S : State) : Prop :=
  (∀ r, r ≠ 3 → r ≠ 11 → S.regs r = S0.regs r) ∧ S.mem = S0.mem ∧ S.fsBase = S0.fsBase ∧ S.xmm 15 = S0.xmm 15 ∧
    S.df = S0.df

/-- **the `trailingZeroBits` loop** from its head (`RBX = i`, words `0 .. i-1` zero) to `enS` with `RBX = tz M`;
`S0` = the state at the loop's first entry (`R10 = mp`, `RDX = ml`) -/
theorem tzLoop {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (S0 : State) (mpB : BitVec 64) (ml X : Nat)
    (hm : ∀ j, j < ml → S0.mem.readLE (mpB.toNat + 8 * j) 8 = Exp.wd X j)
    (hacc : S0.mem.accessible mpB.toNat (8 * ml) false = true) (h48 : mpB.toNat + 8 * ml ≤ 2 ^ 48)
    (hX : 0 < X) (hXl : X < Exp.B ^ ml)
    (h10 : S0.regs 10 = mpB) (h2 : S0.regs 2 = BitVec.ofNat 64 ml)
    (KE : ∀ S' : State, S'.rip = BitVec.ofNat 64 enS → TzKeep S0 S' →
      S'.regs 3 = BitVec.ofNat 64 (Exp.tz X) → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ∀ d i (S : State), ml - i = d → i ≤ ml → (∀ j, j < i → Exp.wd X j = 0) →
      S.rip = BitVec.ofNat 64 tzH → TzKeep S0 S →
      S.regs 3 = BitVec.ofNat 64 i → ReachesRet (LibNE.program.link impl) ret0 S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hz
    exact absurd (words_zero_lt (fun j hj => hz j (by omega)) hXl) (by omega)
  | succ d ih =>
    intro i S hd hi hz hpc hK h3
    obtain ⟨hrg, hmem, hfb, hx, hdf⟩ := hK
    have hil : i < ml := by omega
    have hw64 : Exp.wd X i < 2 ^ 64 := by have := Exp.wd_lt X i; rw [Exp.B_def] at this; exact this
    refine tzStep ret0 Q mpB ml i (Exp.wd X i) S hpc ((hrg 10 (by omega) (by omega)).trans h10)
      ((hrg 2 (by omega) (by omega)).trans h2) h3 hil h48 (hmem ▸ hacc)
      (by rw [hmem, Nat.mul_comm]; exact hm i hil) hw64 ?_ ?_
    · intro hw S' hpc' hm' hf' hx' hd' hr' h3'
      refine ih (i + 1) S' (by omega) (by omega) (fun j hj => ?_) hpc'
        ⟨fun r a b => (hr' r a b).trans (hrg r a b), hm'.trans hmem, hf'.trans hfb, hx'.trans hx, hd'.trans hdf⟩ h3'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact hz j h
      · rw [h]; exact hw
    · intro hw S' hpc' hm' hf' hx' hd' hr' h3'
      refine KE S' hpc'
        ⟨fun r a b => (hr' r a b).trans (hrg r a b), hm'.trans hmem, hf'.trans hfb, hx'.trans hx, hd'.trans hdf⟩ ?_
      rw [h3', Exp.tz_words hz hw]

end FvModexp.Amd64.ExpEven
