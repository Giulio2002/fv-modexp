import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Lib.AddVVAmd64

/-!
# `math/big.addVV(z, x, y []Word) (c Word)` (go-bigmodexpfix arith_amd64.s, Go assembly ABI0, amd64): summary

```
z[i] = (x[i] + y[i] + carry) mod 2^64 for i < len(z), c = final carry          (len(x), len(y) >= len(z))
```

**Summary** (`addVV_summary`, for every length `n = len(z)`): from any state at the entry of `addVV.abi0` whose frame
words describe slices with `x[0:n]`, `y[0:n]` readable and `z[0:n]` writable, in which `z` is equal to or disjoint from
`x` and from `y`, and `z[0:n]` is disjoint from the call frame (return address and the 10 argument/result words), the
function returns (`RET` to the pushed return address) with every register but `RSP` (+8) and `RBP` unspecified, and

* `Σ z_i 2^(64 i) = (Σ x_i 2^(64 i) + Σ y_i 2^(64 i)) mod 2^(64 n)` (values of the limbs BEFORE the call),
* the result word `c = (X + Y) / 2^(64 n)`,
* memory changed only in `z[0:n]` and the result word.

The carry lives in `R10` between the blocks as `0` or `2^64 - 1` (`SBBQ R10, R10`), restored by `ADDQ R10, R10`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.AddVVAmd64 (program entry)

namespace FvModexp.Amd64.AddVVSum

abbrev head1 : Nat := entry + 0x2b
abbrev head4 : Nat := entry + 0x51
abbrev fin : Nat := entry + 0x96

/-- the saved carry `R10` -/
def cw (c : Bool) : BitVec 64 := if c then 18446744073709551615#64 else 0#64

@[simp] theorem cw_def (c : Bool) : cw c = if c = true then 18446744073709551615#64 else 0#64 := rfl

/-- the preconditions at the entry (frame words above the return address: `z, len, cap, x, len, cap, y, len, cap, c`) -/
structure Ctx (s : State) (z x y n : Nat) : Prop where
  hz : s.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  hn : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  hx : s.mem.readLE ((s.regs 4).toNat + 32) 8 = x
  hy : s.mem.readLE ((s.regs 4).toNat + 56) 8 = y
  hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  fb : (s.regs 4).toNat + 88 ≤ 2 ^ 48
  facc : s.mem.accessible (s.regs 4).toNat 88 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azf : Apart z (8 * n) (s.regs 4).toNat 88

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)
    (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)

/-- the memory after the call -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      (lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
        lv s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)) %
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  m.readLE ((s.regs 4).toNat + 80) 8 =
      (lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
        lv s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)) /
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]

/-- the restored carry of `ADDQ R10, R10` -/
@[simp] theorem cw_carry (c : Bool) :
    (decide (18446744073709551616 ≤ (if c = true then 18446744073709551615 else 0) +
      if c = true then 18446744073709551615 else 0)).toNat = c.toNat := by
  cases c <;> decide

/-- one limb of an add-with-carry -/
theorem adc_nat (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c ≤ 1) :
    (a + b + c) % 2 ^ 64 + 2 ^ 64 * (decide (2 ^ 64 ≤ a + b + c)).toNat = a + b + c := by
  by_cases h : 2 ^ 64 ≤ a + b + c
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

theorem toNat_le_one (c : Bool) : c.toNat ≤ 1 := by cases c <;> simp

theorem dec_le_one (p : Prop) [Decidable p] : (decide p).toNat ≤ 1 := toNat_le_one _

/-- the invariant step of one limb -/
theorem step1 (m m' : Memory) (z x y i : Nat) (c : Bool)
    (hv : lv m' z i + 2 ^ (64 * i) * c.toNat = lv m x i + lv m y i) :
    lv (m'.writeLE (z + 8 * i) 8 (m.readLE (x + 8 * i) 8 + m.readLE (y + 8 * i) 8 + c.toNat)) z (i + 1) +
        2 ^ (64 * (i + 1)) * (decide (2 ^ 64 ≤ m.readLE (x + 8 * i) 8 + m.readLE (y + 8 * i) 8 + c.toNat)).toNat =
      lv m x (i + 1) + lv m y (i + 1) := by
  rw [lv_write_succ, lv_succ m x, lv_succ m y, pow_succ64]
  have key := adc_nat (m.readLE (x + 8 * i) 8) (m.readLE (y + 8 * i) 8) c.toNat (limb_lt _ _) (limb_lt _ _)
    (toNat_le_one c)
  exact add_step _ _ _ _ _ _ _ _ _ _ hv (by omega)

/-- the invariant step of a block of four limbs -/
theorem step4 (m m' : Memory) (z x y i : Nat) (c : Bool)
    (hv : lv m' z i + 2 ^ (64 * i) * c.toNat = lv m x i + lv m y i) :
    let a0 := m.readLE (x + 8 * i) 8; let a1 := m.readLE (x + 8 * i + 8) 8
    let a2 := m.readLE (x + 8 * i + 16) 8; let a3 := m.readLE (x + 8 * i + 24) 8
    let b0 := m.readLE (y + 8 * i) 8; let b1 := m.readLE (y + 8 * i + 8) 8
    let b2 := m.readLE (y + 8 * i + 16) 8; let b3 := m.readLE (y + 8 * i + 24) 8
    let c1 := (decide (2 ^ 64 ≤ a0 + b0 + c.toNat)).toNat
    let c2 := (decide (2 ^ 64 ≤ a1 + b1 + c1)).toNat
    let c3 := (decide (2 ^ 64 ≤ a2 + b2 + c2)).toNat
    lv ((((m'.writeLE (z + 8 * i) 8 (a0 + b0 + c.toNat)).writeLE (z + 8 * i + 8) 8 (a1 + b1 + c1)).writeLE
        (z + 8 * i + 16) 8 (a2 + b2 + c2)).writeLE (z + 8 * i + 24) 8 (a3 + b3 + c3)) z (i + 4) +
        2 ^ (64 * (i + 4)) * (decide (2 ^ 64 ≤ a3 + b3 + c3)).toNat =
      lv m x (i + 4) + lv m y (i + 4) := by
  intro a0 a1 a2 a3 b0 b1 b2 b3 c1 c2 c3
  rw [lv_write4, lv_add4, lv_add4, pow_i4]
  have k0 := adc_nat a0 b0 c.toNat (limb_lt _ _) (limb_lt _ _) (toNat_le_one c)
  have k1 := adc_nat a1 b1 c1 (limb_lt _ _) (limb_lt _ _) (dec_le_one _)
  have k2 := adc_nat a2 b2 c2 (limb_lt _ _) (limb_lt _ _) (dec_le_one _)
  have k3 := adc_nat a3 b3 c3 (limb_lt _ _) (limb_lt _ _) (dec_le_one _)
  have hsum : (a0 + b0 + c.toNat) % 2 ^ 64 + 2 ^ 64 * ((a1 + b1 + c1) % 2 ^ 64) +
      2 ^ 128 * ((a2 + b2 + c2) % 2 ^ 64) + 2 ^ 192 * ((a3 + b3 + c3) % 2 ^ 64) +
      2 ^ 256 * (decide (2 ^ 64 ≤ a3 + b3 + c3)).toNat =
      (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) +
        c.toNat := by
    omega
  exact add_step _ _ _ _ _ _ _ _ _ _ hv hsum

/-- the equations every loop state shares with the entry state `s` -/
structure Same (s S : State) : Prop where
  r4 : S.regs 4 = s.regs 4
  r5 : S.regs 5 = s.regs 5
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  mx : S.mxcsr = s.mxcsr
  x87 : S.x87 = s.x87
  fw : S.fpucw = s.fpucw

/-- closes `Same s S'` for a state `S'` reached from a `Same s S` state without touching `RSP`/`RBP` -/
macro "same_tac " h:ident : tactic => `(tactic| (
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := $h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | exact h4
  · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | exact h5
  · first | rfl | exact hfs
  · first | rfl | exact hdf
  · first | rfl | exact hmx
  · first | rfl | exact h87
  · first | rfl | exact hfw))

theorem Same.upd {s S : State} (hs : Same s S) {R : Nat → BitVec 64} (r f m)
    (h4 : R 4 = s.regs 4) (h5 : R 5 = s.regs 5) :
    Same s { S with regs := R, rip := r, flags := f, mem := m } :=
  ⟨h4, h5, hs.fs, hs.df, hs.mx, hs.x87, hs.fw⟩

theorem fin_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) (S : State) (c : Bool)
    (hpc : S.rip = BitVec.ofNat 64 fin) (h10 : S.regs 10 = cw c)
    (hv : lv S.mem z n + 2 ^ (64 * n) * c.toNat = lv s.mem x n + lv s.mem y n)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)]) (hs : Same s S) :
    ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hy, hr, hfb, hfacc, accz, accx, accy, alx, aly, azf⟩ := hc
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs
  unfold Apart at azf
  have hra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  simp only [cw_def] at h10
  janus64_run [Q]
  have hZ := lv_lt S.mem z n
  have hP : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have hcl := toNat_le_one c
  have e : lv (S.mem.writeLE ((s.regs 4).toNat + 80) 8 c.toNat) z n = lv S.mem z n := by
    unfold lv; exact Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨hfs, hfw, h87, ?_, ?_, ?_⟩
  · rw [e, ← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hZ]
  · rw [← hv, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hZ]; omega
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _
      (r := ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)) (by simp) (Nat.le_refl _) (by omega)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1

theorem rd_frame {m m' : Memory} {z i x n a : Nat} (hf : MemFrame m m' [(z, z + 8 * i)])
    (hal : z = x ∨ Apart z (8 * n) x (8 * n)) (hin : x + 8 * i ≤ a) (hle : a + 8 ≤ x + 8 * n) (hi : i ≤ n) :
    m'.readLE a 8 = m.readLE a 8 :=
  hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hal; omega)

theorem blk_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) :
    ∀ k (S : State) (i : Nat) (c : Bool), i + 4 * (k + 1) = n →
      S.rip = BitVec.ofNat 64 head4 → S.regs 3 = BitVec.ofNat 64 (k + 1) →
      S.regs 6 = BitVec.ofNat 64 (x + 8 * i) → S.regs 7 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 8 = BitVec.ofNat 64 (z + 8 * i) → S.regs 10 = cw c →
      lv S.mem z i + 2 ^ (64 * i) * c.toNat = lv s.mem x i + lv s.mem y i →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hr, hfb, hfacc, accz, accx, accy, alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have by' := Arm64.Memory.accessible_bound _ accy
  intro k
  induction k with
  | zero =>
    intro S i c hi hpc h3 h6 h7 h8 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    simp only [cw_def] at h10
    have hn4 : n = i + 4 := by omega
    subst hn4
    janus64_run until [fin]
    simp only [cw_carry]
    refine fin_lem s hc _ _ rfl ?_ (step4 s.mem S.mem z x y i c hv) (frame_ext4 hf _ _ _ _) ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, cw_def, decide_eq_true_eq]
    · same_tac hs
  | succ k ih =>
    intro S i c hi hpc h3 h6 h7 h8 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    simp only [cw_def] at h10
    janus64_run until [head4]
    simp only [cw_carry]
    refine ih _ (i + 4) _ (by omega) rfl ?_ ?_ ?_ ?_ ?_ (step4 s.mem S.mem z x y i c hv) (frame_ext4 hf _ _ _ _) ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, cw_def, decide_eq_true_eq]
    · same_tac hs

theorem one_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) :
    ∀ j (S : State) (i : Nat) (c : Bool), i + (j + 1) = n % 4 →
      S.rip = BitVec.ofNat 64 head1 → S.regs 9 = BitVec.ofNat 64 (j + 1) → S.regs 3 = BitVec.ofNat 64 (n / 4) →
      S.regs 6 = BitVec.ofNat 64 (x + 8 * i) → S.regs 7 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 8 = BitVec.ofNat 64 (z + 8 * i) → S.regs 10 = cw c →
      lv S.mem z i + 2 ^ (64 * i) * c.toNat = lv s.mem x i + lv s.mem y i →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hr, hfb, hfacc, accz, accx, accy, alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have by' := Arm64.Memory.accessible_bound _ accy
  intro j
  induction j with
  | zero =>
    intro S i c hi hpc h9 h3 h6 h7 h8 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    simp only [cw_def] at h10
    rcases Nat.eq_zero_or_pos (n / 4) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus64_run until [fin]
      simp only [cw_carry]
      refine fin_lem s hc _ _ rfl ?_ (step1 s.mem S.mem z x y i c hv) (frame_ext hf _) ?_
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, cw_def, decide_eq_true_eq]
      · same_tac hs
    · obtain ⟨q, hq'⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
      janus64_run until [head4]
      simp only [cw_carry]
      refine blk_lem s hc q _ (i + 1) _ (by omega) rfl ?_ ?_ ?_ ?_ ?_ (step1 s.mem S.mem z x y i c hv) (frame_ext hf _) ?_
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [h3, hq']
      all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, cw_def, decide_eq_true_eq]
      · same_tac hs
  | succ j ih =>
    intro S i c hi hpc h9 h3 h6 h7 h8 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    simp only [cw_def] at h10
    janus64_run until [head1]
    simp only [cw_carry]
    refine ih _ (i + 1) _ (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ (step1 s.mem S.mem z x y i c hv) (frame_ext hf _) ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3
    all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, cw_def, decide_eq_true_eq]
    · same_tac hs

theorem main_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) (hpc : s.rip = BitVec.ofNat 64 entry) :
    ReachesRet program (retAddrOf s) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, hr, hfb, hfacc, accz, accx, accy, alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have hn64 : n < 2 ^ 64 := by omega
  have hz0 : lv s.mem z 0 + 2 ^ (64 * 0) * (false : Bool).toNat = lv s.mem x 0 + lv s.mem y 0 := by
    simp [lv_zero]
  have hs0 : Same s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsh : (BitVec.ofNat 64 n >>> 2).toNat = n / 4 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.shiftRight_eq_div_pow]
  janus64_run until [head1, head4, fin]
  · rw [hsh] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    refine fin_lem s hc _ false rfl rfl hz0 (MemFrame.refl _ _) ?_
    same_tac hs0
  · rw [hsh] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
    refine blk_lem s hc q _ 0 false (by omega) rfl ?r3 ?r6 ?r7 ?r8 rfl hz0 (MemFrame.refl _ _) ?hs
    case r3 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; rw [hsh, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hs => same_tac hs0
    all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero]
  · obtain ⟨j, hj⟩ : ∃ j, n % 4 = j + 1 := ⟨n % 4 - 1, by omega⟩
    refine one_lem s hc j _ 0 false (by omega) rfl ?r9 ?r3 ?r6 ?r7 ?r8 rfl hz0 (MemFrame.refl _ _) ?hs
    case r9 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case r3 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; rw [hsh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hs => same_tac hs0
    all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero]

/-- `addVV.abi0` as a callee (library summary: transfers to any program containing these bytes at this address). -/
theorem addVV_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`z, x, y` slice bases, `zl` the length of `z`) -/
theorem ensures (z zl zc x xl xc y yl yc : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, y, yl, yc] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 88)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat =
          (lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 9 1 =
          [BitVec.ofNat 64 ((lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]) := by
  refine Ensures0.of_summary0 addVV_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, alx, aly, azr⟩
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6
    have hfa := hs.frame_accessible
    have hfb := hs.frame_bound
    simp only [List.length_cons, List.length_nil, Janus.Amd64.GoABI.regSP, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc] at hfa hfb
    have hr := hs.ret
    simp only [Amd64.Program.withExit, Janus.Amd64.GoABI.regSP] at hr
    unfold Pre
    rw [a0, a3, a6, a1]
    exact ⟨a0, a1, a3, a6, by rw [hr]; exact hret.user, by omega, hfa, hz1, hx1, hy1, alx, aly, azr⟩
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6
    unfold Q at hq
    rw [a0, a3, a6, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, Janus.Amd64.GoABI.regSP, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [q2]

end FvModexp.Amd64.AddVVSum
