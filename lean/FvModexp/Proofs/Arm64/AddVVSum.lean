import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Lib.AddVVA64

/-!
# `math/big.addVV(z, x, y []Word) (c Word)` (go-bigmodexpfix arith_arm64.s, Go assembly ABI0, arm64): summary

```
z[i] = (x[i] + y[i] + carry) mod 2^64 for i < len(z), c = final carry          (len(x), len(y) >= len(z))
```

**Summary** (`addVV_summary`, for every length `n = len(z)`): from any state at the entry of `addVV.abi0` whose frame
words describe slices with `x[0:n]`, `y[0:n]` readable and `z[0:n]` writable, in which `z` is equal to or disjoint from
`x` and from `y` (the aliasing of the real call sites: `addVV(z, z, y)`, `addVV(z, x, y)` with fresh `z`), and `z` is
disjoint from the result word, the function returns with every register but `R18`, `g`, `FP`, `SP` unspecified and

* `Σ z_i 2^(64 i) = (Σ x_i 2^(64 i) + Σ y_i 2^(64 i)) mod 2^(64 n)` (values of the limbs BEFORE the call),
* the result word `c = (X + Y) / 2^(64 n)`,
* memory changed only in `z[0:n]` and the result word.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.AddVVA64 (program entry)

namespace FvModexp.Arm64.AddVVSum

abbrev head1 : Nat := entry + 0x20
abbrev head4 : Nat := entry + 0x3c
abbrev fin : Nat := entry + 0x6c

/-- the preconditions at the entry (frame words: `z, len, cap, x, len, cap, y, len, cap, c`) -/
structure Ctx (s : State) (z x y n : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hy : s.mem.readLE (s.sp.toNat + 56) 8 = y
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 88 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 80 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 80) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 56) 8)
    (s.mem.readLE (s.sp.toNat + 16) 8)

/-- the memory after the call -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
      (lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
        lv s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8)) %
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  m.readLE (s.sp.toNat + 80) 8 =
      (lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
        lv s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8)) /
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 80, s.sp.toNat + 88)]

theorem adc_fst (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).fst.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
  simp [addWithCarry, BitVec.toNat_ofNat]

theorem adc_c' (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).snd.c.toNat * 2 ^ 64 + (a.toNat + b.toNat + c.toNat) % 2 ^ 64 =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  simp only [addWithCarry, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · have : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 ≠ a.toNat + b.toNat + c.toNat := by omega
    simp only [ne_eq, this, not_false_eq_true, decide_true, Bool.toNat_true]; omega
  · have : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 = a.toNat + b.toNat + c.toNat := Nat.mod_eq_of_lt (by omega)
    simp only [ne_eq, this, not_true_eq_false, decide_false, Bool.toNat_false]; omega


theorem adc_c (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).snd.c.toNat * 2 ^ 64 + (addWithCarry a b c).fst.toNat = a.toNat + b.toNat + c.toNat := by
  rw [adc_fst]; exact adc_c' a b c

def kc (a b : Nat) (c : Bool) : Bool := (addWithCarry (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) c).snd.c
def rs (a b : Nat) (c : Bool) : BitVec 64 := (addWithCarry (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) c).fst

theorem adc4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (c : Bool)
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64)
    (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64) :
    (rs a0 b0 c).toNat + 2 ^ 64 * (rs a1 b1 (kc a0 b0 c)).toNat +
      2 ^ 128 * (rs a2 b2 (kc a1 b1 (kc a0 b0 c))).toNat +
      2 ^ 192 * (rs a3 b3 (kc a2 b2 (kc a1 b1 (kc a0 b0 c)))).toNat +
      2 ^ 256 * (kc a3 b3 (kc a2 b2 (kc a1 b1 (kc a0 b0 c)))).toNat =
    (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) + c.toNat := by
  have h0 := adc_c (BitVec.ofNat 64 a0) (BitVec.ofNat 64 b0) c
  have h1 := adc_c (BitVec.ofNat 64 a1) (BitVec.ofNat 64 b1) (kc a0 b0 c)
  have h2 := adc_c (BitVec.ofNat 64 a2) (BitVec.ofNat 64 b2) (kc a1 b1 (kc a0 b0 c))
  have h3 := adc_c (BitVec.ofNat 64 a3) (BitVec.ofNat 64 b3) (kc a2 b2 (kc a1 b1 (kc a0 b0 c)))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2,
    Nat.mod_eq_of_lt ha3, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2,
    Nat.mod_eq_of_lt hb3] at h0 h1 h2 h3
  unfold rs kc at *
  omega

theorem carry0 (a : BitVec 64) : (addWithCarry a 0#64 false).snd.c.toNat = 0 := by
  have h := adc_c a 0#64 false
  have := a.isLt
  simp only [BitVec.toNat_ofNat, Bool.toNat_false] at h
  have h2 := adc_fst a 0#64 false
  simp only [BitVec.toNat_ofNat, Bool.toNat_false, Nat.mod_eq_of_lt (by omega : (0 : Nat) < 2 ^ 64)] at h2
  simp at h2 h
  omega

theorem fin_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) (S : State) (c : Bool)
    (hpc : S.pc = BitVec.ofNat 64 fin) (hcf : S.flags.c = c)
    (hv : lv S.mem z n + 2 ^ (64 * n) * c.toNat = lv s.mem x n + lv s.mem y n)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)])
    (hsp : S.sp = s.sp) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.regs 29) (h30 : S.regs 30 = s.regs 30) (hfp : S.fpcr = s.fpcr)
    (htp : S.tpidr = s.tpidr) (hdc : S.dczid = s.dczid) (hex : S.excl = s.excl)
    (hep : S.exclPass = s.exclPass) :
    ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hy, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc
  janus_run [Q]
  have hcl : S.flags.c.toNat ≤ 1 := by cases S.flags.c <;> simp
  have hZ := lv_lt S.mem z n
  have hP : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have e : lv (S.mem.writeLE (s.sp.toNat + 80) 8 S.flags.c.toNat) z n = lv S.mem z n := by
    unfold lv; exact Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)
  rw [hz, hn, hx, hy]
  subst hcf
  refine ⟨htp, hdc, hex, hep, ?_, ?_, ?_⟩
  · rw [e, ← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hZ]
  · rw [← hv, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hZ]; simp only [Nat.zero_add]; omega
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _ (r := (s.sp.toNat + 80, s.sp.toNat + 88)) (by simp) (Nat.le_refl _) (Nat.le_refl _)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1


theorem blk_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) :
    ∀ k (S : State) (i : Nat) (c : Bool), i + 4 * (k + 1) = n →
      S.pc = BitVec.ofNat 64 head4 → S.regs 0 = BitVec.ofNat 64 (k + 1) →
      S.regs 1 = BitVec.ofNat 64 (x + 8 * i) → S.regs 2 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 3 = BitVec.ofNat 64 (z + 8 * i) → S.flags.c = c →
      lv S.mem z i + 2 ^ (64 * i) * c.toNat = lv s.mem x i + lv s.mem y i →
      MemFrame s.mem S.mem [(z, z + 8 * i)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  intro k
  induction k with
  | zero =>
    intro S i c hi hpc h0 h1 h2 h3 hcf hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have hn4 : n = i + 4 := by omega
    subst hn4
    subst hcf
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx1 : S.mem.readLE (x + 8 * i + 8) 8 = s.mem.readLE (x + 8 * i + 8) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx2 : S.mem.readLE (x + 8 * i + 16) 8 = s.mem.readLE (x + 8 * i + 16) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx3 : S.mem.readLE (x + 8 * i + 24) 8 = s.mem.readLE (x + 8 * i + 24) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have ry0 : S.mem.readLE (y + 8 * i) 8 = s.mem.readLE (y + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have ry1 : S.mem.readLE (y + 8 * i + 8) 8 = s.mem.readLE (y + 8 * i + 8) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have ry2 : S.mem.readLE (y + 8 * i + 16) 8 = s.mem.readLE (y + 8 * i + 16) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have ry3 : S.mem.readLE (y + 8 * i + 24) 8 = s.mem.readLE (y + 8 * i + 24) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    janus_run until [fin]
    simp only [rx0, rx1, rx2, rx3, ry0, ry1, ry2, ry3]
    refine fin_lem s hc _ _ rfl rfl ?_ (frame_ext4 hf _ _ _ _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    · rw [lv_write4, lv_add4, lv_add4]
      simp only [toNat_mod64, pow_i4]
      have key := adc4 (s.mem.readLE (x + 8 * i) 8) (s.mem.readLE (x + 8 * i + 8) 8)
        (s.mem.readLE (x + 8 * i + 16) 8) (s.mem.readLE (x + 8 * i + 24) 8)
        (s.mem.readLE (y + 8 * i) 8) (s.mem.readLE (y + 8 * i + 8) 8)
        (s.mem.readLE (y + 8 * i + 16) 8) (s.mem.readLE (y + 8 * i + 24) 8) S.flags.c
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _)
      simp only [rs, kc] at key
      have := add_step (2 ^ (64 * i)) (2 ^ 256) (lv S.mem z i) S.flags.c.toNat (lv s.mem x i) (lv s.mem y i) _ _ _ _ hv key
      exact this
    all_goals janus_simp
  | succ k ih =>
    intro S i c hi hpc h0 h1 h2 h3 hcf hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    subst hcf
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx1 : S.mem.readLE (x + 8 * i + 8) 8 = s.mem.readLE (x + 8 * i + 8) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx2 : S.mem.readLE (x + 8 * i + 16) 8 = s.mem.readLE (x + 8 * i + 16) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx3 : S.mem.readLE (x + 8 * i + 24) 8 = s.mem.readLE (x + 8 * i + 24) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have ry0 : S.mem.readLE (y + 8 * i) 8 = s.mem.readLE (y + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have ry1 : S.mem.readLE (y + 8 * i + 8) 8 = s.mem.readLE (y + 8 * i + 8) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have ry2 : S.mem.readLE (y + 8 * i + 16) 8 = s.mem.readLE (y + 8 * i + 16) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have ry3 : S.mem.readLE (y + 8 * i + 24) 8 = s.mem.readLE (y + 8 * i + 24) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    janus_run until [head4]
    refine ih _ (i + 4) _ (by omega) rfl ?_ ?_ ?_ ?_ rfl ?_ (frame_ext4 hf _ _ _ _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [lv_write4, lv_add4, lv_add4]
      simp only [rx0, rx1, rx2, rx3, ry0, ry1, ry2, ry3, toNat_mod64, pow_i4]
      have key := adc4 (s.mem.readLE (x + 8 * i) 8) (s.mem.readLE (x + 8 * i + 8) 8)
        (s.mem.readLE (x + 8 * i + 16) 8) (s.mem.readLE (x + 8 * i + 24) 8)
        (s.mem.readLE (y + 8 * i) 8) (s.mem.readLE (y + 8 * i + 8) 8)
        (s.mem.readLE (y + 8 * i + 16) 8) (s.mem.readLE (y + 8 * i + 24) 8) S.flags.c
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _)
      simp only [rs, kc] at key
      have := add_step (2 ^ (64 * i)) (2 ^ 256) (lv S.mem z i) S.flags.c.toNat (lv s.mem x i) (lv s.mem y i) _ _ _ _ hv key
      exact this
    all_goals janus_simp


theorem one_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) :
    ∀ j (S : State) (i : Nat) (c : Bool), i + (j + 1) = n % 4 →
      S.pc = BitVec.ofNat 64 head1 → S.regs 4 = BitVec.ofNat 64 (j + 1) → S.regs 0 = BitVec.ofNat 64 (n / 4) →
      S.regs 1 = BitVec.ofNat 64 (x + 8 * i) → S.regs 2 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 3 = BitVec.ofNat 64 (z + 8 * i) → S.flags.c = c →
      lv S.mem z i + 2 ^ (64 * i) * c.toNat = lv s.mem x i + lv s.mem y i →
      MemFrame s.mem S.mem [(z, z + 8 * i)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  intro j
  induction j with
  | zero =>
    intro S i c hi hpc h4 h0 h1 h2 h3 hcf hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    subst hcf
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have ry0 : S.mem.readLE (y + 8 * i) 8 = s.mem.readLE (y + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have hstep : lv (S.mem.writeLE (z + 8 * i) 8 (addWithCarry (BitVec.ofNat 64 (s.mem.readLE (x + 8 * i) 8))
        (BitVec.ofNat 64 (s.mem.readLE (y + 8 * i) 8)) S.flags.c).fst.toNat) z (i + 1) +
        2 ^ (64 * (i + 1)) * (addWithCarry (BitVec.ofNat 64 (s.mem.readLE (x + 8 * i) 8))
        (BitVec.ofNat 64 (s.mem.readLE (y + 8 * i) 8)) S.flags.c).snd.c.toNat =
        lv s.mem x (i + 1) + lv s.mem y (i + 1) := by
      rw [lv_write_succ, lv_succ, lv_succ, toNat_mod64, pow_succ64]
      have key := adc_c (BitVec.ofNat 64 (s.mem.readLE (x + 8 * i) 8)) (BitVec.ofNat 64 (s.mem.readLE (y + 8 * i) 8)) S.flags.c
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (limb_lt s.mem (x + 8 * i)), Nat.mod_eq_of_lt (limb_lt s.mem (y + 8 * i))] at key
      exact add_step (2 ^ (64 * i)) (2 ^ 64) _ _ _ _ _ _ _ _ hv (by omega)
    rcases Nat.eq_zero_or_pos (n / 4) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus_run until [fin]
      try simp only [rx0, ry0]
      refine fin_lem s hc _ _ rfl rfl hstep (frame_ext hf _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
      all_goals janus_simp
    · obtain ⟨q, hq'⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
      janus_run until [head4]
      try simp only [rx0, ry0]
      refine blk_lem s hc q _ (i + 1) _ (by omega) rfl ?_ ?_ ?_ ?_ rfl hstep (frame_ext hf _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
      · janus_simp; rw [hq']
      all_goals first
        | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        | janus_simp
  | succ j ih =>
    intro S i c hi hpc h4 h0 h1 h2 h3 hcf hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    subst hcf
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have ry0 : S.mem.readLE (y + 8 * i) 8 = s.mem.readLE (y + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at aly; omega)
    have hstep : lv (S.mem.writeLE (z + 8 * i) 8 (addWithCarry (BitVec.ofNat 64 (s.mem.readLE (x + 8 * i) 8))
        (BitVec.ofNat 64 (s.mem.readLE (y + 8 * i) 8)) S.flags.c).fst.toNat) z (i + 1) +
        2 ^ (64 * (i + 1)) * (addWithCarry (BitVec.ofNat 64 (s.mem.readLE (x + 8 * i) 8))
        (BitVec.ofNat 64 (s.mem.readLE (y + 8 * i) 8)) S.flags.c).snd.c.toNat =
        lv s.mem x (i + 1) + lv s.mem y (i + 1) := by
      rw [lv_write_succ, lv_succ, lv_succ, toNat_mod64, pow_succ64]
      have key := adc_c (BitVec.ofNat 64 (s.mem.readLE (x + 8 * i) 8)) (BitVec.ofNat 64 (s.mem.readLE (y + 8 * i) 8)) S.flags.c
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (limb_lt s.mem (x + 8 * i)), Nat.mod_eq_of_lt (limb_lt s.mem (y + 8 * i))] at key
      exact add_step (2 ^ (64 * i)) (2 ^ 64) _ _ _ _ _ _ _ _ hv (by omega)
    janus_run until [head1]
    try simp only [rx0, ry0]
    refine ih _ (i + 1) _ (by omega) rfl ?_ ?_ ?_ ?_ ?_ rfl hstep (frame_ext hf _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    all_goals first
      | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
      | janus_simp

theorem main_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  have hn64 : n < 2 ^ 64 := by
    have : 8 * n ≤ 2 ^ 48 := by omega
    omega
  have hz0 : lv s.mem z 0 + 2 ^ (64 * 0) * (false : Bool).toNat = lv s.mem x 0 + lv s.mem y 0 := by
    simp [lv_zero]
  have hmod := lsr2_mod n hn64
  janus_run until [head1, head4, fin]
  · -- n = 0
    rw [hmod] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    refine fin_lem s hc _ _ rfl rfl ?_ (frame_zero _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp [lv_zero, carry0]
  · rw [hmod] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
    refine blk_lem s hc q _ 0 _ (by omega) rfl ?_ ?_ ?_ ?_ rfl ?_ (frame_zero _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [lsr2_toNat n hn64, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals janus_simp
    · have := Nat.mod_lt (((BitVec.ofNat 64 n).rotateRight 2).toNat) (by omega : 0 < 4611686018427387904)
      rw [Nat.div_eq_of_lt (by omega)]
      simp [lv_zero]
  · obtain ⟨j, hj⟩ : ∃ j, n % 4 = j + 1 := ⟨n % 4 - 1, by omega⟩
    refine one_lem s hc j _ 0 _ (by omega) rfl ?_ ?_ ?_ ?_ ?_ rfl ?_ (frame_zero _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [lsr2_toNat n hn64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals janus_simp
    · have := Nat.mod_lt (((BitVec.ofNat 64 n).rotateRight 2).toNat) (by omega : 0 < 4611686018427387904)
      rw [Nat.div_eq_of_lt (by omega)]
      simp [lv_zero]

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
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 80) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat =
          (lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 9 1 =
          [BitVec.ofNat 64 ((lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 80, s.sp.toNat + 88)]) := by
  refine Ensures0.of_summary0 addVV_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, alx, aly, azr⟩
    have h1 := hret.aligned
    have h2 := hret.user
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6
    unfold Pre
    rw [a0, a3, a6, a1]
    refine ⟨a0, a1, a3, a6, ?_, ?_, hs.spAligned, hs.frame_bound, hs.frame_accessible, hz1, hx1, hy1, alx, aly, azr⟩
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6
    unfold Q at hq
    rw [a0, a3, a6, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [show s.sp.toNat + 8 + 8 * 9 = s.sp.toNat + 80 by omega, q2]

end FvModexp.Arm64.AddVVSum

