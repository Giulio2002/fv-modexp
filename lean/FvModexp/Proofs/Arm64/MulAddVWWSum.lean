import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmMul
import FvModexp.Proofs.Lib.MulAddVWWA64

/-!
# `math/big.mulAddVWW(z, x []Word, m, a Word) (c Word)` (go-bigmodexpfix arith_arm64.s, Go assembly ABI0, arm64): summary

```
z[0:n] = x[0:n] * m + a   (n = len(z)),   c = the carry word out of limb n-1       (len(x) >= len(z))
```

**Summary** (`mulAddVWW_summary`, for every length `n = len(z)`): from any state at the entry of `mulAddVWW.abi0` whose
frame words describe slices with `x[0:n]` readable and `z[0:n]` writable, in which `z` is equal to or disjoint from `x`
(every call site in the package: `mulAddVWW(z, x, ..)` with fresh `z` (natmul.go:144), `mulAddVWW(qhatv, v, ..)`
(natdiv.go:693), and the in-place `mulAddVWW(larger, larger, b, 0)` (natconv.go:533)), and `z` is disjoint from the
result word, the function returns with every register but `R18`, `g`, `FP`, `SP` unspecified and

* `Σ z_i 2^(64 i) = (X·m + a) mod 2^(64 n)` where `X = Σ x_i 2^(64 i)` (limbs BEFORE the call),
* the result word `c = (X·m + a) / 2^(64 n)`,
* memory changed only in `z[0:n]` and the result word.

Go source (math/big/arith.go:244 `mulAddVWW_g`; asm arith_arm64.s `TEXT ·mulAddVWW`): a 1x loop for `n mod 8` limbs,
then an 8x unrolled loop; each block is `UMULH/MUL`, `ADDS`, `ADCS`..., `ADC ZR` (`mulblk8`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.MulAddVWWA64 (program entry)

namespace FvModexp.Arm64.MulAddVWWSum

abbrev head1 : Nat := entry + 0x20
abbrev head8 : Nat := entry + 0x44
abbrev fin : Nat := entry + 0xd0

/-- the preconditions at the entry (frame words: `z, len, cap, x, len, cap, m, a, c`) -/
structure Ctx (s : State) (z x n m a : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hm : s.mem.readLE (s.sp.toNat + 56) 8 = m
  ha : s.mem.readLE (s.sp.toNat + 64) 8 = a
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 80 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 72 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 72) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
    (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 64) 8)

/-- the memory after the call -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
      (lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
          s.mem.readLE (s.sp.toNat + 56) 8 + s.mem.readLE (s.sp.toNat + 64) 8) %
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  m.readLE (s.sp.toNat + 72) 8 =
      (lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
          s.mem.readLE (s.sp.toNat + 56) 8 + s.mem.readLE (s.sp.toNat + 64) 8) /
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 72, s.sp.toNat + 80)]

theorem fin_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) (S : State)
    (hpc : S.pc = BitVec.ofNat 64 fin)
    (hv : lv S.mem z n + 2 ^ (64 * n) * (S.regs 1).toNat = lv s.mem x n * m + a)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)])
    (hsp : S.sp = s.sp) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.regs 29) (h30 : S.regs 30 = s.regs 30) (hfp : S.fpcr = s.fpcr)
    (htp : S.tpidr = s.tpidr) (hdc : S.dczid = s.dczid) (hex : S.excl = s.excl)
    (hep : S.exclPass = s.exclPass) :
    ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hm, ha, hl4, hl56, hal, hfb, hfacc, accz, accx, alx, azr⟩ := hc
  janus_run [Q]
  have hZ := lv_lt S.mem z n
  have hP : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have e : lv (S.mem.writeLE (s.sp.toNat + 72) 8 (S.regs 1).toNat) z n = lv S.mem z n := by
    unfold lv; exact Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)
  rw [hz, hn, hx, hm, ha]
  refine ⟨htp, hdc, hex, hep, ?_, ?_, ?_⟩
  · rw [e, ← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hZ]
  · rw [← hv, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hZ]; simp only [Nat.zero_add]
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _ (r := (s.sp.toNat + 72, s.sp.toNat + 80)) (by simp) (Nat.le_refl _) (Nat.le_refl _)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1

set_option exponentiation.threshold 1024 in
theorem blk_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) :
    ∀ k (S : State) (i : Nat), i + 8 * (k + 1) = n →
      S.pc = BitVec.ofNat 64 head8 → S.regs 2 = BitVec.ofNat 64 (k + 1) → S.regs 0 = BitVec.ofNat 64 m →
      S.regs 3 = BitVec.ofNat 64 (x + 8 * i) → S.regs 4 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * (S.regs 1).toNat = lv s.mem x i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hm, ha, hl4, hl56, hal, hfb, hfacc, accz, accx, alx, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hm64 : m < 2 ^ 64 := hm ▸ limb_lt _ _
  intro k
  induction k with
  | zero =>
    intro S i hi hpc h2 h0 h3 h4 hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have hn8 : n = i + 8 := by omega
    subst hn8
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx1 : S.mem.readLE (x + 8 * i + 8) 8 = s.mem.readLE (x + 8 * i + 8) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx2 : S.mem.readLE (x + 8 * i + 16) 8 = s.mem.readLE (x + 8 * i + 16) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx3 : S.mem.readLE (x + 8 * i + 24) 8 = s.mem.readLE (x + 8 * i + 24) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx4 : S.mem.readLE (x + 8 * i + 32) 8 = s.mem.readLE (x + 8 * i + 32) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx5 : S.mem.readLE (x + 8 * i + 40) 8 = s.mem.readLE (x + 8 * i + 40) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx6 : S.mem.readLE (x + 8 * i + 48) 8 = s.mem.readLE (x + 8 * i + 48) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx7 : S.mem.readLE (x + 8 * i + 56) 8 = s.mem.readLE (x + 8 * i + 56) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    janus_run until [fin]
    simp only [rx0, rx1, rx2, rx3, rx4, rx5, rx6, rx7]
    refine fin_lem s hc _ rfl ?_ (frame_ext8 hf _ _ _ _ _ _ _ _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    · rw [lv_write8, lv_add8]
      simp only [toNat_mod64, pow_i8]
      have key := mulblk8 (s.mem.readLE (x + 8 * i) 8) (s.mem.readLE (x + 8 * i + 8) 8) (s.mem.readLE (x + 8 * i + 16) 8) (s.mem.readLE (x + 8 * i + 24) 8) (s.mem.readLE (x + 8 * i + 32) 8) (s.mem.readLE (x + 8 * i + 40) 8) (s.mem.readLE (x + 8 * i + 48) 8) (s.mem.readLE (x + 8 * i + 56) 8)
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (BitVec.ofNat 64 m) (S.regs 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
      exact mul_step _ _ _ _ _ _ _ _ _ _ hv key
    all_goals janus_simp
  | succ k ih =>
    intro S i hi hpc h2 h0 h3 h4 hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx1 : S.mem.readLE (x + 8 * i + 8) 8 = s.mem.readLE (x + 8 * i + 8) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx2 : S.mem.readLE (x + 8 * i + 16) 8 = s.mem.readLE (x + 8 * i + 16) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx3 : S.mem.readLE (x + 8 * i + 24) 8 = s.mem.readLE (x + 8 * i + 24) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx4 : S.mem.readLE (x + 8 * i + 32) 8 = s.mem.readLE (x + 8 * i + 32) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx5 : S.mem.readLE (x + 8 * i + 40) 8 = s.mem.readLE (x + 8 * i + 40) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx6 : S.mem.readLE (x + 8 * i + 48) 8 = s.mem.readLE (x + 8 * i + 48) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have rx7 : S.mem.readLE (x + 8 * i + 56) 8 = s.mem.readLE (x + 8 * i + 56) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    janus_run until [head8]
    simp only [rx0, rx1, rx2, rx3, rx4, rx5, rx6, rx7]
    refine ih _ (i + 8) (by omega) rfl ?_ ?_ ?_ ?_ ?_ (frame_ext8 hf _ _ _ _ _ _ _ _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · janus_simp
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [lv_write8, lv_add8]
      simp only [toNat_mod64, pow_i8]
      have key := mulblk8 (s.mem.readLE (x + 8 * i) 8) (s.mem.readLE (x + 8 * i + 8) 8) (s.mem.readLE (x + 8 * i + 16) 8) (s.mem.readLE (x + 8 * i + 24) 8) (s.mem.readLE (x + 8 * i + 32) 8) (s.mem.readLE (x + 8 * i + 40) 8) (s.mem.readLE (x + 8 * i + 48) 8) (s.mem.readLE (x + 8 * i + 56) 8)
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (BitVec.ofNat 64 m) (S.regs 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
      exact mul_step _ _ _ _ _ _ _ _ _ _ hv key
    all_goals janus_simp

theorem one_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) :
    ∀ j (S : State) (i : Nat), i + (j + 1) = n % 8 →
      S.pc = BitVec.ofNat 64 head1 → S.regs 5 = BitVec.ofNat 64 (j + 1) → S.regs 2 = BitVec.ofNat 64 (n / 8) →
      S.regs 0 = BitVec.ofNat 64 m →
      S.regs 3 = BitVec.ofNat 64 (x + 8 * i) → S.regs 4 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * (S.regs 1).toNat = lv s.mem x i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hm, ha, hl4, hl56, hal, hfb, hfacc, accz, accx, alx, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hm64 : m < 2 ^ 64 := hm ▸ limb_lt _ _
  intro j
  induction j with
  | zero =>
    intro S i hi hpc h5 h2 h0 h3 h4 hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have hstep : lv (S.mem.writeLE (z + 8 * i) 8 ((ml (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m)).toNat +
          (S.regs 1).toNat)) z (i + 1) +
        2 ^ (64 * (i + 1)) * (addWithCarry (mh (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m)) 0#64
          (addWithCarry (ml (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m)) (S.regs 1) false).snd.c).fst.toNat =
        lv s.mem x (i + 1) * m + a := by
      rw [lv_write_succ, lv_succ, pow_succ64]
      have key := mul1 (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m) (S.regs 1) (limb_lt _ _)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
      exact mul_step _ _ _ _ _ _ _ _ _ _ hv key
    rcases Nat.eq_zero_or_pos (n / 8) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus_run until [fin]
      try simp only [rx0]
      refine fin_lem s hc _ rfl hstep (frame_ext hf _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
      all_goals janus_simp
    · obtain ⟨q, hq'⟩ : ∃ q, n / 8 = q + 1 := ⟨n / 8 - 1, by omega⟩
      janus_run until [head8]
      try simp only [rx0]
      refine blk_lem s hc q _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_ hstep (frame_ext hf _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
      · janus_simp; rw [hq']
      all_goals first
        | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        | janus_simp
  | succ j ih =>
    intro S i hi hpc h5 h2 h0 h3 h4 hv hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have rx0 : S.mem.readLE (x + 8 * i) 8 = s.mem.readLE (x + 8 * i) 8 :=
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at alx; omega)
    have hstep : lv (S.mem.writeLE (z + 8 * i) 8 ((ml (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m)).toNat +
          (S.regs 1).toNat)) z (i + 1) +
        2 ^ (64 * (i + 1)) * (addWithCarry (mh (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m)) 0#64
          (addWithCarry (ml (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m)) (S.regs 1) false).snd.c).fst.toNat =
        lv s.mem x (i + 1) * m + a := by
      rw [lv_write_succ, lv_succ, pow_succ64]
      have key := mul1 (s.mem.readLE (x + 8 * i) 8) (BitVec.ofNat 64 m) (S.regs 1) (limb_lt _ _)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
      exact mul_step _ _ _ _ _ _ _ _ _ _ hv key
    janus_run until [head1]
    try simp only [rx0]
    refine ih _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ hstep (frame_ext hf _) rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    all_goals first
      | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
      | janus_simp

theorem main_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg7, hl4, hl56, hal, hfb, hfacc, accz, accx, alx, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hm64 : m < 2 ^ 64 := h_rd_arg6 ▸ limb_lt _ _
  have ha64 : a < 2 ^ 64 := h_rd_arg7 ▸ limb_lt _ _
  have hn64 : n < 2 ^ 64 := by
    have : 8 * n ≤ 2 ^ 48 := by omega
    omega
  have hmod := lsr3_mod n hn64
  janus_run until [head1, head8, fin]
  · -- n = 0
    rw [hmod] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    refine fin_lem s hc _ rfl ?_ (frame_zero _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp [lv_zero]
    janus_simp
  · rw [hmod] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 8 = q + 1 := ⟨n / 8 - 1, by omega⟩
    refine blk_lem s hc q _ 0 (by omega) rfl ?_ ?_ ?_ ?_ ?_ (frame_zero _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [lsr3_toNat n hn64, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals janus_simp
    · simp [lv_zero]
  · obtain ⟨j, hj⟩ : ∃ j, n % 8 = j + 1 := ⟨n % 8 - 1, by omega⟩
    refine one_lem s hc j _ 0 (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ (frame_zero _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [and7_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [lsr3_toNat n hn64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals janus_simp
    · simp [lv_zero]

/-- `mulAddVWW.abi0` as a callee (library summary: transfers to any program containing these bytes at this address). -/
theorem mulAddVWW_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`z, x` slice bases, `zl` the length of `z`, multiplier `m`, addend `a`) -/
theorem ensures (z zl zc x xl xc m a : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, m, a] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 72) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat =
          (lv s.mem x.toNat zl.toNat * m.toNat + a.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 8 1 =
          [BitVec.ofNat 64 ((lv s.mem x.toNat zl.toNat * m.toNat + a.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 72, s.sp.toNat + 80)]) := by
  refine Ensures0.of_summary0 mulAddVWW_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, alx, azr⟩
    have h1 := hret.aligned
    have h2 := hret.user
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a7 := hs.arg (i := 7) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6 a7
    unfold Pre
    rw [a0, a3, a6, a7, a1]
    refine ⟨a0, a1, a3, a6, a7, ?_, ?_, hs.spAligned, hs.frame_bound, hs.frame_accessible, hz1, hx1, alx, azr⟩
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a7 := hs.arg (i := 7) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6 a7
    unfold Q at hq
    rw [a0, a3, a6, a7, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [show s.sp.toNat + 8 + 8 * 8 = s.sp.toNat + 72 by omega, q2]

end FvModexp.Arm64.MulAddVWWSum
