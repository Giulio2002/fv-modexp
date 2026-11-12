import FvModexp.Proofs.Arm64.Exp.P2DDefs
import FvModexp.Proofs.Arm64.Exp.EvTz

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `i := x.trailingZeroBits()` (nat.go:944, inlined; agent infra)

The loop at `tzH = 0x1b5a44` (`R11 = i`, `x` in `R4`/`R5`; `panicBounds` at `i = len x` unreachable for `0 < X`), by
induction on `xl - i` (adapted from infra's `ExpEven.tzLoop`); exit `tzX = 0x1b5a64` with `R11 = tz X`,
`R13 = y[0]`. Pure segment: memory, `sp` and every register but `R11`/`R12`/`R13` unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

abbrev tzH' : Nat := 1792580
abbrev tzX : Nat := 1792612

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `trailingZeroBits` loop** from its head (`X1 = i`, words `0 .. i-1` zero) to `enS` with `X1 = tz M` -/
theorem tzLoopP {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (mp ml X yp : Nat) (M : Memory)
    (rg : Nat → BitVec 64) (sp : BitVec 64)
    (hm : ∀ j, j < ml → M.readLE (mp + 8 * j) 8 = Exp.wd X j)
    (hacc : M.accessible mp (8 * ml) false = true) (h48 : mp + 8 * ml ≤ 2 ^ 48)
    (hX : 0 < X) (hXl : X < Exp.B ^ ml) (hml : ml ≤ 2 ^ 12)
    (hya : M.accessible yp 8 false = true) (hyp : yp < 2 ^ 64)
    (h10 : rg 4 = BitVec.ofNat 64 mp) (h11 : rg 5 = BitVec.ofNat 64 ml) (h7 : rg 7 = BitVec.ofNat 64 yp)
    (KE : ∀ S' : State, S'.pc = BitVec.ofNat 64 tzX → S'.sp = sp → (∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → S'.regs r = rg r) →
      S'.regs 11 = BitVec.ofNat 64 (Exp.tz X) → S'.regs 13 = BitVec.ofNat 64 (M.readLE yp 8) → S'.mem = M →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ∀ d i (S : State), ml - i = d → i ≤ ml → (∀ j, j < i → Exp.wd X j = 0) →
      S.pc = BitVec.ofNat 64 tzH' → S.sp = sp → (∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → S.regs r = rg r) →
      S.regs 11 = BitVec.ofNat 64 i → S.mem = M → ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hz
    exact absurd (ExpEven.words_zero_lt (fun j hj => hz j (by omega)) hXl) (by omega)
  | succ d ih =>
    intro i S hd hi hz hpc hsp hrg h1 hmem
    have hil : i < ml := by omega
    have r4 : S.regs 4 = BitVec.ofNat 64 mp := (hrg 4 (by omega) (by omega) (by omega)).trans h10
    have r5 : S.regs 5 = BitVec.ofNat 64 ml := (hrg 5 (by omega) (by omega) (by omega)).trans h11
    have r7 : S.regs 7 = BitVec.ofNat 64 yp := (hrg 7 (by omega) (by omega) (by omega)).trans h7
    have hrd : M.readLE (mp + i * 8) 8 = Exp.wd X i := by rw [Nat.mul_comm]; exact hm i hil
    have hw64 : Exp.wd X i < 2 ^ 64 := by have := Exp.wd_lt X i; rw [Exp.B_def] at this; exact this
    by_cases hw : Exp.wd X i = 0
    · janus_run [hrd, hw] until [tzH']
      refine ih (i + 1) _ (by omega) (by omega) (fun j hj => ?_) rfl rfl (fun r a b c => ?_) ?_ rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact hz j h
        · rw [h]; exact hw
      · simp only [setReg_apply, if_neg a, if_neg b, if_neg c]; exact hrg r a b c
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
      janus_run [hrd, hc, hya] until [tzX]
      refine KE _ rfl rfl (fun r a b c => ?_) ?_ (by janus_simp) rfl
      · simp only [setReg_apply, if_neg a, if_neg b, if_neg c]; exact hrg r a b c
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [htz]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show Exp.tz (Exp.wd X i) < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show i * 64 < 2 ^ 64 by omega)]
        omega


end FvModexp.Arm64.P2D

namespace FvModexp.Arm64.P2D

abbrev rshE : Nat := 1785296
abbrev rshR : Nat := 1792716

/-- the memory at the `rsh` call: the spills of `st, logM, cap z, len z, cap y, len y, y.ptr, z.ptr, lo` -/
@[reducible] def W1 (M : Memory) (sp st lm zc zl yc yl yp zp lo : Nat) : Memory :=
  ((((((((M.writeLE (sp + 144) 8 st).writeLE (sp + 200) 8 lm).writeLE (sp + 136) 8 zc).writeLE (sp + 128) 8 zl).writeLE
    (sp + 192) 8 yc).writeLE (sp + 184) 8 yl).writeLE (sp + 176) 8 yp).writeLE (sp + 120) 8 zp).writeLE (sp + 96) 8 lo

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **after the loop**: `tz · y[0]` overflow or `≥ logM` → `zero2`; else the spills and the entry of
`rsh(nil, x, tz)` -/
theorem tzE (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (sp zp zl zc st xp xl xc yp yl yc lm tz y0 : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 208 ≤ 2 ^ 48) (hacc : M.accessible (sp + 96) 112 true = true)
    (hz : zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ yp < 2 ^ 64 ∧ yl < 2 ^ 64 ∧ yc < 2 ^ 64 ∧
      lm < 2 ^ 64 ∧ tz < 2 ^ 64 ∧ y0 < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 tzX) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 lm)
    (h11 : S.regs 11 = BitVec.ofNat 64 tz) (h13 : S.regs 13 = BitVec.ofNat 64 y0) (hmem : S.mem = M)
    (KZ : (tz * y0 / 2 ^ 64 ≠ 0 ∨ lm ≤ tz * y0 % 2 ^ 64) → ∀ S' : State, S'.pc = BitVec.ofNat 64 1792632 →
      S'.sp = S.sp → S'.regs 0 = S.regs 0 → S'.regs 2 = S.regs 2 → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.mem = M → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KR : tz * y0 < 2 ^ 64 → tz * y0 < lm → ∀ S' : State, S'.pc = BitVec.ofNat 64 rshE → S'.sp = S.sp →
      S'.regs 0 = 0#64 → S'.regs 1 = 0#64 → S'.regs 2 = 0#64 → S'.regs 3 = BitVec.ofNat 64 xp →
      S'.regs 4 = BitVec.ofNat 64 xl → S'.regs 5 = BitVec.ofNat 64 xc → S'.regs 6 = BitVec.ofNat 64 tz →
      S'.regs 30 = BitVec.ofNat 64 rshR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.mem = W1 M sp st lm zc zl yc yl yp zp (tz * y0) →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hz
  have hm : (BitVec.ofNat 64 tz * BitVec.ofNat 64 y0).toNat = tz * y0 % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt z9, Nat.mod_eq_of_lt z10]
  generalize e18 : S.regs 18 = x18 at KZ KR
  generalize e28 : S.regs 28 = x28 at KZ KR
  generalize e29 : S.regs 29 = x29 at KR
  generalize eS : S.sp = xsp at KZ KR
  generalize e0 : S.regs 0 = x0 at KZ
  generalize e2 : S.regs 2 = x2 at KZ
  subst hmem
  janus_run [hm] until [1792632, rshE]
  · have hlo : tz * y0 < 2 ^ 64 := by
      have := Nat.div_add_mod (tz * y0) (2 ^ 64); rw [(by janus_assumption : tz * y0 / 18446744073709551616 = 0)] at this; omega
    refine KR hlo hbr _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    · rw [← eS, hsp]
  · exact KZ (Or.inr (by omega)) _ rfl (by rw [← eS, hsp]) (by janus_simp; rw [← e0, h0]) (by janus_simp; rw [← e2, h2])
      (by janus_simp) (by janus_simp) rfl
  · exact KZ (Or.inl (by janus_assumption)) _ rfl (by rw [← eS, hsp]) (by janus_simp; rw [← e0, h0]) (by janus_simp; rw [← e2, h2])
      (by janus_simp) (by janus_simp) rfl

end FvModexp.Arm64.P2D
