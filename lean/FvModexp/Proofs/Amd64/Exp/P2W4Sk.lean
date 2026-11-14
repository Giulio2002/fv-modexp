import FvModexp.Proofs.Amd64.Exp.P2W4Defs
import FvModexp.Proofs.Common.ExpPow2

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `mmask`, `mtop`, the first word and the skip-zero loop (nat.go:1163-1196)
(agent divmc s76, port of divmc s68; amd64 twin of agent infra's `Arm64.P2W4Sk`)

From the table's return (fn+0x289): `mmask` (R10; `-1` when `(logM-1) % 64 = 0`), `mtop = (logM-2) >> 6` (R11),
`i = min(len y - 1, mtop)` (R11), `yi = y[i]` (R15, `& mmask` iff `i == mtop`), then the loop at `skH` (fn+0x30a,
`TESTQ R15, R15`; `for yi == 0 { if i == 0 { return 1 }; i--; yi = y[i] }`). Model: `Exp.skipZero y i yi`. Exits:
`blE` (fn+0x3d8, `bitLen`; `skipZero = some (i, yi)`) and `r1E` (fn+0x32a, return 1; `skipZero = none`). Pure segment:
memory unchanged. Registers at the exits: `AX = logM`, `R11 = i`, `R12 = len y`, `R13 = y`, `R15 = yi`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the skip loop's head `TESTQ R15, R15` (fn+0x30a) -/
abbrev skH : Nat := 6198752
/-- `bitLen(yi)` (fn+0x3d8, the loop's exit with `yi ≠ 0`) -/
abbrev blE : Nat := 6198955
/-- `return 1` (fn+0x32a) -/
abbrev r1E : Nat := 6198780

/-- the registers this pure segment keeps -/
@[reducible] def Kp (sp g : Nat) (r5 : W64) (fsB : W64) (dfB : Bool) (M : Memory) (S : State) : Prop :=
  S.regs 4 = BitVec.ofNat 64 sp ∧ S.regs 14 = BitVec.ofNat 64 g ∧ S.regs 5 = r5 ∧ S.xmm 15 = 0 ∧
    S.fsBase = fsB ∧ S.df = dfB ∧ S.mem = M

/-- the continuation at `bitLen` -/
@[reducible] def KBl (impl : List Amd64.Segment) (ret0 : W64) (Q : State → Prop) (sp g lm yp yl : Nat) (M : Memory)
    (r5 fsB : W64) (dfB : Bool) (v : Option (Nat × Nat)) : Prop :=
  ∀ (S' : State) (i yi : Nat), S'.rip = BitVec.ofNat 64 blE → Kp sp g r5 fsB dfB M S' →
    S'.regs 0 = BitVec.ofNat 64 lm → S'.regs 12 = BitVec.ofNat 64 yl → S'.regs 11 = BitVec.ofNat 64 i →
    S'.regs 13 = BitVec.ofNat 64 yp → S'.regs 15 = BitVec.ofNat 64 yi → i < yl → 0 < yi → yi < 2 ^ 64 →
    v = some (i, yi) → ReachesRet (LibW.program.link impl) ret0 S' Q

/-- the continuation at `return 1` -/
@[reducible] def KR1 (impl : List Amd64.Segment) (ret0 : W64) (Q : State → Prop) (sp g : Nat) (M : Memory)
    (r5 fsB : W64) (dfB : Bool) (v : Option (Nat × Nat)) : Prop :=
  ∀ (S' : State), S'.rip = BitVec.ofNat 64 r1E → Kp sp g r5 fsB dfB M S' → v = none →
    ReachesRet (LibW.program.link impl) ret0 S' Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the skip-zero loop** from its head, by induction on `i` -/
theorem skipLoop {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp g lm yp yl Y : Nat) (M : Memory)
    (r5 fsB : W64) (dfB : Bool)
    (hy : ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd Y j)
    (hacc : M.accessible yp (8 * yl) false = true) (hy48 : yp + 8 * yl ≤ 2 ^ 48) (hyl : yl ≤ 2 ^ 12)
    (v : Option (Nat × Nat))
    (KB : KBl impl ret0 Q sp g lm yp yl M r5 fsB dfB v) (KR : KR1 impl ret0 Q sp g M r5 fsB dfB v) :
    ∀ i (S : State) (yi : Nat), S.rip = BitVec.ofNat 64 skH → Kp sp g r5 fsB dfB M S →
      S.regs 0 = BitVec.ofNat 64 lm → S.regs 12 = BitVec.ofNat 64 yl → S.regs 11 = BitVec.ofNat 64 i →
      S.regs 13 = BitVec.ofNat 64 yp → S.regs 15 = BitVec.ofNat 64 yi → i < yl → yi < 2 ^ 64 →
      Exp.skipZero Y i yi = v → ReachesRet (LibW.program.link impl) ret0 S Q := by
  intro i
  induction i with
  | zero =>
    intro S yi hpc ⟨h4, h14, h5, hx15, hfs, hdf, hm⟩ h0 h12 h11 h13 h15 hi hyi hv
    janus64_run until [blE, r1E]
    · exact KR _ rfl ⟨h4, h14, h5, hx15, hfs, rfl, rfl⟩ (by rw [← hv, hbr]; rfl)
    · exact KB _ 0 yi rfl ⟨h4, h14, h5, hx15, hfs, rfl, rfl⟩ h0 h12 h11 h13 h15 hi (by omega) hyi
        (by rw [← hv]; simp [Exp.skipZero, hbr])
  | succ i ih =>
    intro S yi hpc ⟨h4, h14, h5, hx15, hfs, hdf, hm⟩ h0 h12 h11 h13 h15 hi hyi hv
    have hrd : M.readLE (yp + (i + 1) * 8 - 8) 8 = Exp.wd Y i := by
      rw [show yp + (i + 1) * 8 - 8 = yp + 8 * i by omega]; exact hy i (by omega)
    have ha : M.accessible (yp + (i + 1) * 8 - 8) 8 false = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    have e1 : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hrd, ha] until [blE, r1E, skH]
    · have hb0 : yi = 0 := by janus_assumption
      refine ih _ (Exp.wd Y i) rfl ⟨?_, ?_, ?_, hx15, hfs, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_ (by omega)
        (by have := Exp.wd_lt Y i; simp only [Exp.B] at this; exact this) ?_
      all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e1]
      · exact h4
      · exact h14
      · exact h5
      · exact h0
      · exact h12
      · exact h13
      · rw [← hv, hb0]; rfl
    · exact KB _ (i + 1) yi rfl ⟨h4, h14, h5, hx15, hfs, rfl, rfl⟩ h0 h12 h11 h13 h15 hi (by omega) hyi
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
theorem skipHead {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp g lm yp yl Y : Nat) (M : Memory)
    (r5 fsB : W64) (dfB : Bool) (hsp : sp + 0x358 ≤ 2 ^ 48) (hlm2 : 2 ≤ lm) (hlm : lm ≤ 2 ^ 13) (hyl0 : 0 < yl)
    (hy : ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd Y j)
    (hacc : M.accessible yp (8 * yl) false = true) (hy48 : yp + 8 * yl ≤ 2 ^ 48) (hyl : yl ≤ 2 ^ 12)
    (a1d8 : M.accessible (sp + 0x300) 16 false = true) (a228 : M.accessible (sp + 0x350) 8 false = true)
    (r1d8 : M.readLE (sp + 0x300) 8 = yp) (r1e0 : M.readLE (sp + 0x308) 8 = yl) (r228 : M.readLE (sp + 0x350) 8 = lm)
    (KB : KBl impl ret0 Q sp g lm yp yl M r5 fsB dfB (Exp.skipZero Y (i0 lm yl) (yi0 lm yl Y)))
    (KR : KR1 impl ret0 Q sp g M r5 fsB dfB (Exp.skipZero Y (i0 lm yl) (yi0 lm yl Y)))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6198613) (hK : Kp sp g r5 fsB dfB M S) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨h4, h14, h5, hx15, hfs, hdf, hm⟩ := hK
  have e2 : BitVec.ofNat 64 yl - 1#64 = BitVec.ofNat 64 (yl - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e3 : BitVec.ofNat 64 lm - 1#64 = BitVec.ofNat 64 (lm - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e1 : BitVec.ofNat 64 lm - 2#64 = BitVec.ofNat 64 (lm - 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e4 : BitVec.ofNat 64 (lm - 2) >>> 6 = BitVec.ofNat 64 ((lm - 2) / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e5 : 1#64 <<< ((lm - 1) % 64) = BitVec.ofNat 64 (2 ^ ((lm - 1) % 64)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide), Nat.one_mul]
  have hrd : ∀ j, j = i0 lm yl → M.readLE (yp + j * 8) 8 = Exp.wd Y (i0 lm yl) := by
    intro j hj; subst hj; rw [Nat.mul_comm]; exact hy _ (by simp only [i0]; omega)
  have t1 := toInt_small ((lm - 2) / 64) (by omega)
  have t2 := toInt_small (yl - 1) (by omega)
  janus64_run [r1d8, r1e0, r228, a1d8, a228, e1, e2, e3, e4, t1, t2] until [skH]
  all_goals refine (skipLoop ret0 Q sp g lm yp yl Y M r5 fsB dfB hy hacc hy48 hyl _ KB KR (i0 lm yl) _ (yi0 lm yl Y)
    rfl ⟨?_, ?_, ?_, hx15, hfs, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_ (by simp only [i0]; omega) (yi0_lt lm yl Y) rfl)
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h4, h14, h5, e5]
  all_goals first
    | exact congrArg (BitVec.ofNat 64) (by simp only [i0]; omega)
    | exact yiC (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega)
    | exact yiA (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega) (by omega)
    | exact yiB (hrd _ (by simp only [i0]; omega)) (by simp only [i0]; omega) (by omega)

end FvModexp.Amd64.P2W4
