import FvModexp.Proofs.Arm64.Exp.EvDefs
import FvModexp.Proofs.Arm64.Exp.P2W2Sk

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `n := m.trailingZeroBits()` (nat.go:364-374, inlined; agent infra)

The loop at `tzH = 0x1b52f8` (`for i < len(m) { if m[i] != 0 { return i*64 + TrailingZeros64(m[i]) } }`;
`panicBounds` at `i = len m` is unreachable for `0 < M`), by induction on `ml - i`; exit `enS` with `X1 = tz M`
(`Exp.tz_words`, `Exp.ctz_rbit`). Pure segment: memory, `sp` and every register but `X1`/`X13` unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem words_zero_lt {X ml : Nat} (hz : ∀ j, j < ml → Exp.wd X j = 0) (hX : X < Exp.B ^ ml) : X = 0 := by
  have := Exp.mod_B_pow_zero X ml hz; rwa [Nat.mod_eq_of_lt hX] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `trailingZeroBits` loop** from its head (`X1 = i`, words `0 .. i-1` zero) to `enS` with `X1 = tz M` -/
theorem tzLoop {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (mp ml X : Nat) (M : Memory)
    (rg : Nat → BitVec 64) (sp : BitVec 64)
    (hm : ∀ j, j < ml → M.readLE (mp + 8 * j) 8 = Exp.wd X j)
    (hacc : M.accessible mp (8 * ml) false = true) (h48 : mp + 8 * ml ≤ 2 ^ 48)
    (hX : 0 < X) (hXl : X < Exp.B ^ ml) (hml : ml ≤ 2 ^ 12)
    (h10 : rg 10 = BitVec.ofNat 64 mp) (h11 : rg 11 = BitVec.ofNat 64 ml)
    (KE : ∀ S' : State, S'.pc = BitVec.ofNat 64 enS → S'.sp = sp → (∀ r, r ≠ 1 → r ≠ 13 → S'.regs r = rg r) →
      S'.regs 1 = BitVec.ofNat 64 (Exp.tz X) → S'.mem = M → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ∀ d i (S : State), ml - i = d → i ≤ ml → (∀ j, j < i → Exp.wd X j = 0) →
      S.pc = BitVec.ofNat 64 tzH → S.sp = sp → (∀ r, r ≠ 1 → r ≠ 13 → S.regs r = rg r) →
      S.regs 1 = BitVec.ofNat 64 i → S.mem = M → ReachesRet (LibNE.program.link impl) ret0 S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hz
    exact absurd (words_zero_lt (fun j hj => hz j (by omega)) hXl) (by omega)
  | succ d ih =>
    intro i S hd hi hz hpc hsp hrg h1 hmem
    have hil : i < ml := by omega
    have r10 : S.regs 10 = BitVec.ofNat 64 mp := (hrg 10 (by omega) (by omega)).trans h10
    have r11 : S.regs 11 = BitVec.ofNat 64 ml := (hrg 11 (by omega) (by omega)).trans h11
    have hrd : M.readLE (mp + i * 8) 8 = Exp.wd X i := by rw [Nat.mul_comm]; exact hm i hil
    have hw64 : Exp.wd X i < 2 ^ 64 := by have := Exp.wd_lt X i; rw [Exp.B_def] at this; exact this
    by_cases hw : Exp.wd X i = 0
    · janus_run [hrd, hw] until [tzH]
      refine ih (i + 1) _ (by omega) (by omega) (fun j hj => ?_) rfl rfl (fun r a b => ?_) ?_ rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact hz j h
        · rw [h]; exact hw
      · simp only [setReg_apply, if_neg a, if_neg b]; exact hrg r a b
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · have hc := Exp.ctz_rbit hw hw64
      have ht : Exp.tz (Exp.wd X i) < 64 := by
        have hs := (Exp.tz_spec (x := Exp.wd X i) (by omega)).1
        have hq : 0 < Exp.wd X i / 2 ^ Exp.tz (Exp.wd X i) := by
          rcases Nat.eq_zero_or_pos (Exp.wd X i / 2 ^ Exp.tz (Exp.wd X i)) with h0 | h0
          · rw [h0, Nat.mul_zero] at hs; omega
          · exact h0
        have : 2 ^ Exp.tz (Exp.wd X i) ≤ Exp.wd X i := by
          calc 2 ^ Exp.tz (Exp.wd X i) ≤ 2 ^ Exp.tz (Exp.wd X i) * (Exp.wd X i / 2 ^ Exp.tz (Exp.wd X i)) :=
                Nat.le_mul_of_pos_right _ hq
            _ = Exp.wd X i := hs.symm
        exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt this hw64)
      have htz := Exp.tz_words hz hw
      janus_run [hrd, hc] until [enS]
      refine KE _ rfl rfl (fun r a b => ?_) ?_ rfl
      · simp only [setReg_apply, if_neg a, if_neg b]; exact hrg r a b
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [htz]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show Exp.tz (Exp.wd X i) < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show i * 64 < 2 ^ 64 by omega)]
        omega

end FvModexp.Arm64.ExpEven
