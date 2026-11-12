import FvModexp.Proofs.Arm64.Exp.P2W2Defs
import FvModexp.Proofs.Common.ExpPow2

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `mmask`, `mtop`, the first word and the skip-zero loop (nat.go:1163-1196)
(agent infra)

From the table's return `0x1b65f4 = 1795572`: `mmask` (R8), `mtop = (logM-2) >> 6`, `i = min(len y - 1, mtop)`,
`yi = y[i]` (`& mmask` iff `i == mtop`), then the loop at `0x1b665c = 1795676` (`for yi == 0 { if i == 0 { return 1 };
i--; yi = y[i] }`). Model: `Exp.skipZero y i yi`. Exits: `0x1b66f4 = 1795828` (bitLen; `skipZero = some (i, yi)`) and
`0x1b6674 = 1795700` (return 1; `skipZero = none`). Pure segment: memory unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the skip loop's head `CBNZ R13` -/
abbrev skH : Nat := 1795676
/-- `bitLen(yi)` (the loop's exit with `yi ≠ 0`) -/
abbrev blE : Nat := 1795828
/-- `return 1` -/
abbrev r1E : Nat := 1795700

/-- the continuation at `bitLen` -/
@[reducible] def KBl (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (sp g lm yp yl : Nat) (M : Memory)
    (r18 r29 : BitVec 64) (v : Option (Nat × Nat)) : Prop :=
  ∀ (S' : State) (i yi : Nat), S'.pc = BitVec.ofNat 64 blE → S'.sp = BitVec.ofNat 64 sp →
    S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.regs 18 = r18 → S'.mem = M →
    S'.regs 2 = BitVec.ofNat 64 lm → S'.regs 10 = BitVec.ofNat 64 yl → S'.regs 11 = BitVec.ofNat 64 i →
    S'.regs 12 = BitVec.ofNat 64 yp → S'.regs 13 = BitVec.ofNat 64 yi → i < yl → 0 < yi → yi < 2 ^ 64 →
    v = some (i, yi) → ReachesRet (LibExp.program.link impl) ret0 S' Q

/-- the continuation at `return 1` -/
@[reducible] def KR1 (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (sp g : Nat) (M : Memory)
    (r18 r29 : BitVec 64) (v : Option (Nat × Nat)) : Prop :=
  ∀ (S' : State), S'.pc = BitVec.ofNat 64 r1E → S'.sp = BitVec.ofNat 64 sp →
    S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.regs 18 = r18 → S'.mem = M →
    S'.regs 7 = 1#64 → v = none → ReachesRet (LibExp.program.link impl) ret0 S' Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the skip-zero loop** from its head, by induction on `i` -/
theorem skipLoop {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp g lm yp yl Y : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (hy : ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd Y j)
    (hacc : M.accessible yp (8 * yl) false = true) (hy48 : yp + 8 * yl ≤ 2 ^ 48) (hyl : yl ≤ 2 ^ 12)
    (v : Option (Nat × Nat))
    (KB : KBl impl ret0 Q sp g lm yp yl M r18 r29 v) (KR : KR1 impl ret0 Q sp g M r18 r29 v) :
    ∀ i (S : State) (yi : Nat), S.pc = BitVec.ofNat 64 skH → S.sp = BitVec.ofNat 64 sp →
      S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 → S.regs 18 = r18 → S.mem = M →
      S.regs 2 = BitVec.ofNat 64 lm → S.regs 10 = BitVec.ofNat 64 yl → S.regs 11 = BitVec.ofNat 64 i →
      S.regs 12 = BitVec.ofNat 64 yp → S.regs 13 = BitVec.ofNat 64 yi → S.regs 7 = 1#64 → i < yl → yi < 2 ^ 64 →
      Exp.skipZero Y i yi = v → ReachesRet (LibExp.program.link impl) ret0 S Q := by
  intro i
  induction i with
  | zero =>
    intro S yi hpc hsp h28 h29 h18 hm h2 h10 h11 h12 h13 h7 hi hyi hv
    janus_run until [blE, r1E]
    · exact KR _ rfl rfl h28 h29 h18 rfl h7 (by rw [← hv, hbr]; rfl)
    · exact KB _ 0 yi rfl rfl h28 h29 h18 rfl h2 h10 h11 h12 h13 hi (by omega) hyi
        (by rw [← hv]; simp [Exp.skipZero, hbr])
  | succ i ih =>
    intro S yi hpc hsp h28 h29 h18 hm h2 h10 h11 h12 h13 h7 hi hyi hv
    janus_run until [blE, r1E, skH]
    · have hb0 : yi = 0 := by janus_assumption
      refine ih _ (Exp.wd Y i) rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ rfl ?_ (by omega)
        (by have := Exp.wd_lt Y i; simp only [Exp.B] at this; exact this) ?_
      all_goals first | (janus_simp; done) | skip
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · rw [← hv, hb0]; rfl
      all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18, h2, h10, h12, h7]
    · exact KB _ (i + 1) yi rfl rfl h28 h29 h18 rfl h2 h10 h11 h12 h13 hi (by omega) hyi
        (by rw [← hv]; simp [Exp.skipZero, hbr])

theorem and_ones (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

theorem and_mask (a k : Nat) (ha : a < 2 ^ 64) (hk : k < 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ k) - 1#64 = BitVec.ofNat 64 (a % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 (2 ^ k) - 1#64).toNat = 2 ^ k - 1 := by
    have : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem toInt_small (a : Nat) (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `i = min(len y - 1, mtop)` (nat.go:1171-1174) -/
@[reducible] def i0 (lm yl : Nat) : Nat := min (yl - 1) ((lm - 2) / 64)
/-- `yi = y[i]`, masked by `mmask` iff `i == mtop` (nat.go:1177-1180), as in `Exp.p2win` -/
@[reducible] def yi0 (lm yl Y : Nat) : Nat :=
  if i0 lm yl = (lm - 2) / 64 then (if (lm - 1) % 64 ≠ 0 then Exp.wd Y (i0 lm yl) % 2 ^ ((lm - 1) % 64)
    else Exp.wd Y (i0 lm yl)) else Exp.wd Y (i0 lm yl)

theorem yi0_lt (lm yl Y : Nat) : yi0 lm yl Y < 2 ^ 64 := by
  have := Exp.wd_lt Y (i0 lm yl); simp only [Exp.B] at this
  simp only [yi0]; split <;> (try split) <;> first | exact this | exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) this

theorem yiA {lm yl Y r : Nat} (hr : r = Exp.wd Y (i0 lm yl)) (h1 : i0 lm yl = (lm - 2) / 64)
    (h2 : (lm - 1) % 64 = 0) : BitVec.ofNat 64 r &&& 18446744073709551615#64 = BitVec.ofNat 64 (yi0 lm yl Y) := by
  rw [and_ones, hr]; simp only [yi0, h1, h2, ↓reduceIte, ne_eq, not_true_eq_false]

theorem yiB {lm yl Y r : Nat} (hr : r = Exp.wd Y (i0 lm yl)) (h1 : i0 lm yl = (lm - 2) / 64)
    (h2 : ¬(lm - 1) % 64 = 0) :
    BitVec.ofNat 64 r &&& BitVec.ofNat 64 (2 ^ ((lm - 1) % 64)) - 1#64 = BitVec.ofNat 64 (yi0 lm yl Y) := by
  have := Exp.wd_lt Y (i0 lm yl); simp only [Exp.B] at this
  rw [and_mask _ _ (by omega) (Nat.mod_lt _ (by omega)), hr]
  simp only [yi0, h1, h2, ↓reduceIte, ne_eq, not_false_eq_true]

theorem yiC {lm yl Y r : Nat} (hr : r = Exp.wd Y (i0 lm yl)) (h1 : ¬i0 lm yl = (lm - 2) / 64) :
    BitVec.ofNat 64 r = BitVec.ofNat 64 (yi0 lm yl Y) := by
  rw [hr]; simp only [yi0, h1, ↓reduceIte]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **from the table's return** to the skip loop -/
theorem skipHead {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp g lm yp yl Y : Nat) (M : Memory)
    (r18 r29 : BitVec 64) (hal : sp % 16 = 0) (hlm2 : 2 ≤ lm) (hlm : lm ≤ 2 ^ 13) (hyl0 : 0 < yl) (hsp : sp + 560 ≤ 2 ^ 48)
    (hy : ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd Y j)
    (hacc : M.accessible yp (8 * yl) false = true) (hy48 : yp + 8 * yl ≤ 2 ^ 48) (hyl : yl ≤ 2 ^ 12)
    (hsacc : M.accessible (sp + 528) 32 false = true)
    (r528 : M.readLE (sp + 528) 8 = yp) (r536 : M.readLE (sp + 536) 8 = yl) (r552 : M.readLE (sp + 552) 8 = lm)
    (KB : KBl impl ret0 Q sp g lm yp yl M r18 r29 (Exp.skipZero Y (i0 lm yl) (yi0 lm yl Y)))
    (KR : KR1 impl ret0 Q sp g M r18 r29 (Exp.skipZero Y (i0 lm yl) (yi0 lm yl Y)))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1795572) (hspS : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (h18 : S.regs 18 = r18) (hm : S.mem = M) :
    ReachesRet (LibExp.program.link impl) ret0 S Q := by
  have e1 : BitVec.ofNat 64 lm - 2#64 = BitVec.ofNat 64 (lm - 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e2 : BitVec.ofNat 64 yl - 1#64 = BitVec.ofNat 64 (yl - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e3 : BitVec.ofNat 64 lm - 1#64 = BitVec.ofNat 64 (lm - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e4 : BitVec.ofNat 64 (lm - 2) >>> 6 = BitVec.ofNat 64 ((lm - 2) / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have t1 := toInt_small ((lm - 2) / 64) (by omega)
  have t2 := toInt_small (yl - 1) (by omega)
  have hrd : ∀ j, j = i0 lm yl → M.readLE (yp + j * 8) 8 = Exp.wd Y (i0 lm yl) := by
    intro j hj; subst hj; rw [Nat.mul_comm]; exact hy _ (by simp only [i0]; omega)
  janus_run [r528, r536, r552, e1, e2, e3, e4, t1, t2, TruncMath.rot6] until [skH]
  all_goals refine (skipLoop ret0 Q sp g lm yp yl Y M r18 r29 hy hacc hy48 hyl _ KB KR (i0 lm yl) _ (yi0 lm yl Y)
    rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [i0]; omega) (yi0_lt lm yl Y) rfl)
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18]
  · exact congrArg _ (by simp only [i0]; omega)
  · exact yiA (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega) (by omega)
  · exact congrArg _ (by simp only [i0]; omega)
  · exact yiC (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega)
  · exact congrArg _ (by simp only [i0]; omega)
  · exact yiA (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega) (by omega)
  · exact congrArg _ (by simp only [i0]; omega)
  · exact yiB (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega) (by omega)
  · exact congrArg _ (by simp only [i0]; omega)
  · exact yiC (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega)
  · exact congrArg _ (by simp only [i0]; omega)
  · exact yiB (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega) (by omega)

end FvModexp.Arm64.P2W2
