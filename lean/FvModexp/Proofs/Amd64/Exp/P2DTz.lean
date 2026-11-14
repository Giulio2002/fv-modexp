import FvModexp.Proofs.Amd64.Exp.P2DEnt
import FvModexp.Proofs.Amd64.Exp.EvTz

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `i := x.trailingZeroBits()` (nat.go:944, inlined; agent asm s66; twin of infra's
arm64 `P2DTz`, adapted from asm's amd64 `ExpEven.tzLoop`)

The loop at `tzH = 0x5e912f` (`R12 = i`, `x` in `RSI`/`R8`; `panicBounds` at `i = len x` unreachable for `0 < X`), by
induction on `xl - i`; exit `tzX = 0x5e9153` (after `R15 := y[0]`, `SHLQ $6, R12; BSFQ R13, R13; ADDQ R13, R12`) with
`R12 = tz X`, `R15 = [R11]`. Only `R12`, `R13`, `R15`, `RIP`, flags change.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

abbrev tzX : Nat := 0x5e9153

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- one loop iteration from the head `tzH` (`R12 = i < xl`, word `w = [xp + 8i]`): zero word → back at `tzH` with
`R12 = i + 1`; non-zero → `tzX` with `R12 = 64 i + tz w`, `R15 = [R11]` -/
theorem tzStep {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (xpB ypB : BitVec 64) (xl i w : Nat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 tzH) (r6 : S.regs 6 = xpB) (r8 : S.regs 8 = BitVec.ofNat 64 xl)
    (r11 : S.regs 11 = ypB) (r12 : S.regs 12 = BitVec.ofNat 64 i) (hil : i < xl) (h48 : xpB.toNat + 8 * xl ≤ 2 ^ 48)
    (hacc : S.mem.accessible xpB.toNat (8 * xl) false = true)
    (hya : S.mem.accessible ypB.toNat 8 false = true) (hy48 : ypB.toNat + 8 ≤ 2 ^ 48)
    (hrd : S.mem.readLE (xpB.toNat + i * 8) 8 = w) (hw64 : w < 2 ^ 64)
    (K0 : w = 0 → ∀ S' : State, S'.rip = BitVec.ofNat 64 tzH → S'.mem = S.mem → S'.fsBase = S.fsBase →
      S'.xmm 15 = S.xmm 15 → S'.df = S.df → (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 15 → S'.regs r = S.regs r) →
      S'.regs 12 = BitVec.ofNat 64 (i + 1) → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K1 : w ≠ 0 → ∀ S' : State, S'.rip = BitVec.ofNat 64 tzX → S'.mem = S.mem → S'.fsBase = S.fsBase →
      S'.xmm 15 = S.xmm 15 → S'.df = S.df → (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 15 → S'.regs r = S.regs r) →
      S'.regs 12 = BitVec.ofNat 64 (64 * i + Exp.tz w) →
      S'.regs 15 = BitVec.ofNat 64 (S.mem.readLE ypB.toNat 8) → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hxl : xl < 2 ^ 46 := by omega
  have hacc' : S.mem.accessible (xpB.toNat + i * 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  by_cases hw : w = 0
  · subst hw
    janus64_run [hrd] until [tzH]
    refine K0 rfl _ rfl rfl rfl rfl rfl (fun r a b c => ?_) ?_
    · janus64_simp; try simp only [if_neg a, if_neg b, if_neg c]
    · janus64_simp
  · have hc := ExpEven.ctz_eq hw hw64
    have ht := ExpEven.tz_wd_lt hw hw64
    janus64_run [hrd, hc] until [tzX]
    refine K1 hw _ rfl rfl rfl rfl rfl (fun r a b c => ?_) ?_ ?_
    · janus64_simp; try simp only [if_neg a, if_neg b, if_neg c]
    · janus64_simp
      apply BitVec.eq_of_toNat_eq
      have hi : i < 2 ^ 46 := by omega
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show i * 2 ^ 6 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show Exp.tz w < 2 ^ 64 by omega)]
      omega
    · janus64_simp

/-- what the loop keeps: every register but `R12`/`R13`/`R15`, memory, FS base, `X15`, `DF` -/
@[reducible] def TzKeep (S0 S : State) : Prop :=
  (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 15 → S.regs r = S0.regs r) ∧ S.mem = S0.mem ∧ S.fsBase = S0.fsBase ∧
    S.xmm 15 = S0.xmm 15 ∧ S.df = S0.df

/-- **the `trailingZeroBits` loop** from its head (`R12 = i`, words `0 .. i-1` zero) to `tzX` with `R12 = tz X`;
`S0` = the state at the loop's first entry (`RSI = xp`, `R8 = xl`, `R11 = yp`) -/
theorem tzLoop {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (S0 : State) (xpB ypB : BitVec 64)
    (xl X : Nat)
    (hm : ∀ j, j < xl → S0.mem.readLE (xpB.toNat + 8 * j) 8 = Exp.wd X j)
    (hacc : S0.mem.accessible xpB.toNat (8 * xl) false = true) (h48 : xpB.toNat + 8 * xl ≤ 2 ^ 48)
    (hya : S0.mem.accessible ypB.toNat 8 false = true) (hy48 : ypB.toNat + 8 ≤ 2 ^ 48)
    (hX : 0 < X) (hXl : X < Exp.B ^ xl)
    (h6 : S0.regs 6 = xpB) (h8 : S0.regs 8 = BitVec.ofNat 64 xl) (h11 : S0.regs 11 = ypB)
    (KE : ∀ S' : State, S'.rip = BitVec.ofNat 64 tzX → TzKeep S0 S' →
      S'.regs 12 = BitVec.ofNat 64 (Exp.tz X) → S'.regs 15 = BitVec.ofNat 64 (S0.mem.readLE ypB.toNat 8) →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ∀ d i (S : State), xl - i = d → i ≤ xl → (∀ j, j < i → Exp.wd X j = 0) →
      S.rip = BitVec.ofNat 64 tzH → TzKeep S0 S →
      S.regs 12 = BitVec.ofNat 64 i → ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hz
    exact absurd (ExpEven.words_zero_lt (fun j hj => hz j (by omega)) hXl) (by omega)
  | succ d ih =>
    intro i S hd hi hz hpc hK h12
    obtain ⟨hrg, hmem, hfb, hx, hdf⟩ := hK
    have hil : i < xl := by omega
    have hw64 : Exp.wd X i < 2 ^ 64 := by have := Exp.wd_lt X i; rw [Exp.B_def] at this; exact this
    refine tzStep ret0 Q xpB ypB xl i (Exp.wd X i) S hpc ((hrg 6 (by omega) (by omega) (by omega)).trans h6)
      ((hrg 8 (by omega) (by omega) (by omega)).trans h8) ((hrg 11 (by omega) (by omega) (by omega)).trans h11)
      h12 hil h48 (hmem ▸ hacc) (hmem ▸ hya) hy48
      (by rw [hmem, Nat.mul_comm]; exact hm i hil) hw64 ?_ ?_
    · intro hw S' hpc' hm' hf' hx' hd' hr' h12'
      refine ih (i + 1) S' (by omega) (by omega) (fun j hj => ?_) hpc'
        ⟨fun r a b c => (hr' r a b c).trans (hrg r a b c), hm'.trans hmem, hf'.trans hfb, hx'.trans hx,
          hd'.trans hdf⟩ h12'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact hz j h
      · rw [h]; exact hw
    · intro hw S' hpc' hm' hf' hx' hd' hr' h12' h15'
      refine KE S' hpc'
        ⟨fun r a b c => (hr' r a b c).trans (hrg r a b c), hm'.trans hmem, hf'.trans hfb, hx'.trans hx,
          hd'.trans hdf⟩ ?_ (by rw [h15', hmem])
      rw [h12', Exp.tz_words hz hw]

end FvModexp.Amd64.P2D
