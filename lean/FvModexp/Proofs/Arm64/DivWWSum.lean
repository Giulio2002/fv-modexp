import FvModexp.Proofs.Common.AsmDivNat
import FvModexp.Proofs.Common.AsmDivMath
import FvModexp.Proofs.Common.AsmDivEns
import FvModexp.Proofs.Lib.DivWWA64

/-!
# `math/big.divWW(x1, x0, y, m Word) (q, r Word)` (go-bigmodexpfix `src/math/big/arith.go:273`, Go ABIInternal, arm64)

`q = floor((x1*2^64 + x0) / y)`, `r = (x1*2^64 + x0) % y`, for `y != 0`, `x1 < y` and `m = recipWord y`
(`m = floor((2^128-1) / (y << nlz y)) - 2^64`, the value `reciprocalWord(y)` returns, arith.go:333).  The correctness argument
is the comment of arith.go:280-330; its mathematics is `FvModexp.AsmDiv.estimate_gen`/`corrections`/`normalise`
(`Common/AsmDivMath.lean`), the machine proof has three parts: the shift (`main`), the multiply/estimate chain and the two
corrections (`tail`, from the pc after the normalisation, `entry + 0x40`).

Registers: `X0 = x1, X1 = x0, X2 = y, X3 = m`; results `X0 = q`, `X1 = r`.  The function is frameless (no stack, no
stack-guard check, no memory access), registers `X0..X9` are clobbered, memory is unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open FvModexp.Lib.DivWWA64 (program entry)
namespace FvModexp.Arm64.DivWWSum

theorem mulhi_toNat (a b : BitVec 64) :
    (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 a * BitVec.setWidth 128 b)).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb; simpa [← Nat.pow_add] using this
  rw [Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 128)]
  generalize a.toNat * b.toNat = p at *
  omega

theorem mullo_toNat (a b : BitVec 64) : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul _ _

theorem t1_val (a0 a1 a3 : BitVec 64) :
    ((addWithCarry (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 a0 * BitVec.setWidth 128 a3)) a0
      (addWithCarry a1 (a0 * a3) false).snd.c).fst).toNat =
    ((a0.toNat * a3.toNat + a1.toNat) / 2 ^ 64 + a0.toNat) % 2 ^ 64 := by
  rw [addWithCarry_fst_toNat, mulhi_toNat, addWithCarry_c64, mullo_toNat]
  have := a0.isLt; have := a1.isLt
  generalize a0.toNat * a3.toNat = p
  have hc : ∀ P : Prop, [Decidable P] → (decide P).toNat = if P then 1 else 0 := by
    intro P _; by_cases h : P <;> simp [h]
  rw [hc]
  simp only [Bool.toNat_false, Nat.add_zero]
  split <;> omega

theorem r_vals (X1 X0 T d : BitVec 64) (hle : d.toNat * T.toNat ≤ X1.toNat * 2 ^ 64 + X0.toNat)
    (hlt : X1.toNat * 2 ^ 64 + X0.toNat < d.toNat * T.toNat + 2 ^ 64 + d.toNat) (hd : d.toNat < 2 ^ 64) :
    (X0 - T * d).toNat = (X1.toNat * 2 ^ 64 + X0.toNat - d.toNat * T.toNat) % 2 ^ 64 ∧
    (addWithCarry X1 (~~~BitVec.extractLsb' 64 64 (BitVec.setWidth 128 T * BitVec.setWidth 128 d))
      (addSub X0 (T * d) true).snd.c).fst.toNat = (X1.toNat * 2 ^ 64 + X0.toNat - d.toNat * T.toNat) / 2 ^ 64 := by
  have hX1 := X1.isLt; have hX0 := X0.isLt
  have hP := Nat.mul_comm d.toNat T.toNat
  rw [addSub, if_pos rfl, addWithCarry_c64, addWithCarry_fst_toNat, BitVec.toNat_not, mulhi_toNat, BitVec.toNat_sub,
    mullo_toNat, BitVec.toNat_not, mullo_toNat]
  have hc : ∀ P : Prop, [Decidable P] → (decide P).toNat = if P then 1 else 0 := by
    intro P _; by_cases h : P <;> simp [h]
  rw [hc]
  generalize T.toNat * d.toNat = P at *
  generalize hQ : d.toNat * T.toNat = P' at *
  have : P = P' := by omega
  subst this
  constructor
  · omega
  · simp only [Bool.toNat_true]
    split <;> omega

theorem tail (s : State) (Q : State → Prop) (hpc : s.pc = BitVec.ofNat 64 (entry + 0x40))
    (hd1 : 2 ^ 63 ≤ (s.regs 2).toNat) (hX1 : (s.regs 0).toNat < (s.regs 2).toNat)
    (hm : (s.regs 3).toNat = (2 ^ 128 - 1) / (s.regs 2).toNat - 2 ^ 64) (hs : (s.regs 4).toNat ≤ 63) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hQ : ∀ s' : State,
      s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat) →
      s'.regs 1 = BitVec.ofNat 64 ((((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat) / 2 ^ (s.regs 4).toNat) →
      (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] → s'.regs i = s.regs i) → s'.sp = s.sp → s'.mem = s.mem →
      s'.pc = s.regs 30 → Q s') :
    ReachesRet program (s.regs 30) s Q := by
  janus_run until [entry + 0x50]
  generalize hF : (addWithCarry (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (s.regs 0) * BitVec.setWidth 128 (s.regs 3))) (s.regs 0) (addWithCarry (s.regs 1) (s.regs 0 * s.regs 3) false).snd.c).snd = fl0
  have hT := t1_val (s.regs 0) (s.regs 1) (s.regs 3)
  generalize (addWithCarry (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (s.regs 0) * BitVec.setWidth 128 (s.regs 3))) (s.regs 0) (addWithCarry (s.regs 1) (s.regs 0 * s.regs 3) false).snd.c).fst = T at *
  janus_run until [entry + 0x60]
  have hd2 := (s.regs 2).isLt
  have hX0 := (s.regs 1).isLt
  have hm' : (s.regs 3).toNat = (2 ^ 128 - 1) / (s.regs 2).toNat - 2 ^ 64 := hm
  have hest := FvModexp.AsmDiv.estimate_gen (2 ^ 64) (s.regs 2).toNat (s.regs 0).toNat (s.regs 1).toNat (s.regs 3).toNat
    (((s.regs 3).toNat * (s.regs 0).toNat + (s.regs 1).toNat) / 2 ^ 64 + (s.regs 0).toNat) (by omega) (by omega) hd2 hX1 hX0
    (by rw [show (2:Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by rw [← Nat.pow_add]] at hm'; exact hm') rfl
  have hTv : T.toNat = ((s.regs 3).toNat * (s.regs 0).toNat + (s.regs 1).toNat) / 2 ^ 64 + (s.regs 0).toNat := by
    rw [hT, Nat.mul_comm (s.regs 0).toNat]; exact Nat.mod_eq_of_lt hest.1
  obtain ⟨hr0, hr1⟩ := r_vals (s.regs 0) (s.regs 1) T (s.regs 2) (by rw [hTv]; exact hest.2.1)
    (by have := hest.2.2; rw [hTv]; omega) hd2
  generalize (s.regs 1 - T * s.regs 2) = r0 at *
  generalize (addWithCarry (s.regs 0) (~~~BitVec.extractLsb' 64 64 (BitVec.setWidth 128 T * BitVec.setWidth 128 (s.regs 2))) (addSub (s.regs 1) (T * s.regs 2) true).snd.c).fst = r1 at *
  generalize (addWithCarry (s.regs 0) (~~~BitVec.extractLsb' 64 64 (BitVec.setWidth 128 T * BitVec.setWidth 128 (s.regs 2))) (addSub (s.regs 1) (T * s.regs 2) true).snd.c).snd = fl1
  janus_run
  have hcor := FvModexp.AsmDiv.corrections (s.regs 2).toNat ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) T.toNat hd1 hd2
    (by rw [hTv]; exact hest.2.1) (by rw [hTv]; exact hest.2.2)
  have hd0 : 0 < (s.regs 2).toNat := by omega
  obtain ⟨X, hXd⟩ : ∃ X, X = (s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d, d = (s.regs 2).toNat := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = X - d * T.toNat := ⟨_, rfl⟩
  rw [← hXd, ← hdd] at hcor hr0 hr1
  rw [← hRd] at hcor hr0 hr1
  have hR1 : r1.toNat = 0 ↔ ¬ 2 ^ 64 ≤ R := by
    rw [hr1]; have := hest.2.2; rw [hTv] at *; omega
  generalize hA : (if r1.toNat = 0 then r0 else r0 - s.regs 2) = ra
  generalize hB : (if r1.toNat = 0 then T else T + 1#64) = qa
  have hXd' : X < d * 2 ^ 64 := by
    rw [hXd, hdd]
    have e : ((s.regs 0).toNat + 1) * 2 ^ 64 ≤ (s.regs 2).toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hX1
    rw [Nat.add_mul] at e; omega
  have hT1 : 2 ^ 64 ≤ R → T.toNat + 1 < 2 ^ 64 := by
    intro hc
    have h1 : d * (T.toNat + 1) < d * 2 ^ 64 := by
      rw [Nat.mul_add, Nat.mul_one]; rw [hRd] at hc; have := hest.2.1; rw [hTv] at *; omega
    have := Nat.lt_of_mul_lt_mul_left h1
    exact this
  have hra : ra.toNat = if 2 ^ 64 ≤ R then (R % 2 ^ 64 + 2 ^ 64 - d) % 2 ^ 64 else R % 2 ^ 64 := by
    rw [← hA]
    by_cases hz : r1.toNat = 0
    · rw [if_pos hz, if_neg (hR1.mp hz), hr0]
    · have hc : 2 ^ 64 ≤ R := by
        by_cases hh : 2 ^ 64 ≤ R
        · exact hh
        · exact absurd (hR1.mpr hh) hz
      rw [if_neg hz, if_pos hc, BitVec.toNat_sub, hr0, ← hdd]
      omega
  have hqa : qa.toNat = if 2 ^ 64 ≤ R then T.toNat + 1 else T.toNat := by
    rw [← hB]
    by_cases hz : r1.toNat = 0
    · rw [if_pos hz, if_neg (hR1.mp hz)]
    · have hc : 2 ^ 64 ≤ R := by
        by_cases hh : 2 ^ 64 ≤ R
        · exact hh
        · exact absurd (hR1.mpr hh) hz
      rw [if_neg hz, if_pos hc, BitVec.toNat_add]
      have := hT1 hc
      simp only [BitVec.toNat_ofNat]
      omega
  have hqlt : X / d < 2 ^ 64 := Nat.div_lt_of_lt_mul hXd'
  have hsh : (s.regs 4).toNat < 64 := by omega
  have hd0' : 0 < d := by omega
  obtain ⟨hcq, hcr⟩ := hcor
  have hcq2 : (if d ≤ ra.toNat then qa.toNat + 1 else qa.toNat) = X / d := by
    rw [hra, hqa]; exact hcq
  have hcr2 : (if d ≤ ra.toNat then (ra.toNat + 2 ^ 64 - d) % 2 ^ 64 else ra.toNat) = X % d := by
    rw [hra]; exact hcr
  apply hQ
  · simp only [setReg, Nat.reduceEqDiff, reduceIte]
    rw [← hXd, ← hdd]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
    by_cases hl : ra.toNat < d
    · rw [if_pos hl]
      rw [if_neg (by omega : ¬ d ≤ ra.toNat)] at hcq2
      exact hcq2
    · rw [if_neg hl, BitVec.toNat_add]
      rw [if_pos (by omega : d ≤ ra.toNat)] at hcq2
      simp only [BitVec.toNat_ofNat]
      omega
  · simp only [setReg, Nat.reduceEqDiff, reduceIte]
    rw [← hXd, ← hdd, if_pos hsh]
    apply BitVec.eq_of_toNat_eq
    have hv : (if d ≤ ra.toNat then ra - s.regs 2 else ra).toNat = X % d := by
      by_cases hl : d ≤ ra.toNat
      · rw [if_pos hl, BitVec.toNat_sub, ← hdd]
        rw [if_pos hl] at hcr2
        rw [← hcr2]
        have := ra.isLt
        omega
      · rw [if_neg hl]; rw [if_neg hl] at hcr2; exact hcr2
    have hmod : (s.regs 4).toNat % 64 = (s.regs 4).toNat := Nat.mod_eq_of_lt hsh
    rw [BitVec.toNat_ushiftRight, hv, Nat.shiftRight_eq_div_pow, hmod, BitVec.toNat_ofNat]
    have : X % d / 2 ^ (s.regs 4).toNat < 2 ^ 64 := by
      have := Nat.mod_lt X hd0'
      have := Nat.div_le_self (X % d) (2 ^ (s.regs 4).toNat)
      omega
    rw [Nat.mod_eq_of_lt this]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [setReg]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
  · rfl
  · rfl
  · rfl

/-- the postcondition of the summary -/
def Post (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧
  s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat) ∧
  s'.regs 1 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat) ∧
  (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] → s'.regs i = s.regs i) ∧ MemFrame s.mem s'.mem []

theorem entry_to_tail (s S : State) (hy : (s.regs 2).toNat ≠ 0) (hx : (s.regs 0).toNat < (s.regs 2).toNat)
    (hm : (s.regs 3).toNat = FvModexp.AsmDiv.recipWord (s.regs 2).toNat)
    (h1 : (s.regs 30).toNat % 4 = 0) (h2 : (s.regs 30).toNat < 2 ^ 56)
    (hpc : S.pc = BitVec.ofNat 64 (entry + 0x40)) (hS30 : S.regs 30 = s.regs 30)
    (hS2 : (S.regs 2).toNat = (s.regs 2).toNat * 2 ^ Janus.Arm64.clzNat 64 (s.regs 2).toNat)
    (hS4 : (S.regs 4).toNat = Janus.Arm64.clzNat 64 (s.regs 2).toNat) (hS3 : S.regs 3 = s.regs 3)
    (hSX : (S.regs 0).toNat * 2 ^ 64 + (S.regs 1).toNat =
      ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) * 2 ^ Janus.Arm64.clzNat 64 (s.regs 2).toNat)
    (hS0 : (S.regs 0).toNat < (S.regs 2).toNat)
    (hSr : ∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] → S.regs i = s.regs i) (hSsp : S.sp = s.sp) (hSm : S.mem = s.mem) :
    ReachesRet program (s.regs 30) S (Post s) := by
  have hn := FvModexp.AsmDiv.clz_norm64 (s.regs 2).toNat hy (s.regs 2).isLt
  rw [← hS30]
  refine tail S _ hpc ?_ hS0 ?_ ?_ ?_ ?_ ?_
  · rw [hS2]; exact hn.2.1
  · rw [hS3, hm, hS2]; rfl
  · rw [hS4]; exact hn.1
  · rw [hS30]; exact h1
  · rw [hS30]; exact h2
  · intro s' e0 e1 hr hsp hmem hp
    rw [hSX, hS2] at e0
    rw [hSX, hS2, hS4] at e1
    obtain ⟨c, hc⟩ : ∃ c, c = Janus.Arm64.clzNat 64 (s.regs 2).toNat := ⟨_, rfl⟩
    rw [← hc] at e0 e1 hn hS2
    obtain ⟨X, hX⟩ : ∃ X, X = (s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat := ⟨_, rfl⟩
    obtain ⟨y, hyd⟩ : ∃ y, y = (s.regs 2).toNat := ⟨_, rfl⟩
    rw [← hX, ← hyd] at e0 e1 
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hp, hS30]
    · rw [hsp, hSsp]
    · rw [← hX, ← hyd, e0, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos c)]
    · rw [← hX, ← hyd, e1, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos c)]
    · intro i hi; rw [hr i hi, hSr i hi]
    · rw [hmem, hSm]; exact MemFrame.refl _ _
  

theorem sh_b (a : BitVec 64) (c : Nat) (hc : c ≤ 63) :
    (if c < 64 then a <<< (c % 64) else 0#64).toNat = a.toNat * 2 ^ c % 2 ^ 64 := by
  rw [if_pos (by omega), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : c < 64)]

theorem sh_a (a b : BitVec 64) (c : Nat) (h1 : 1 ≤ c) (h2 : c ≤ 63) (h : a.toNat * 2 ^ c < 2 ^ 64) :
    ((if c < 64 then a <<< (c % 64) else 0#64) |||
      b >>> ((18446744073709551552 - c - 18446744073709551488) % 64)).toNat = a.toNat * 2 ^ c + b.toNat / 2 ^ (64 - c) := by
  have e : (18446744073709551552 - c - 18446744073709551488) % 64 = 64 - c := by omega
  rw [e, BitVec.toNat_or, sh_b a c h2, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  have hb : b.toNat / 2 ^ (64 - c) < 2 ^ c := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show 64 - c + c = 64 by omega]; exact b.isLt
  rw [FvModexp.AsmDiv.or_hi_comm _ _ _ hb]; omega

/-- the callee summary of `divWW` (arm64) -/
theorem divWW_summary : Summary program entry
   (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ (s.regs 2).toNat ≠ 0 ∧
      (s.regs 0).toNat < (s.regs 2).toNat ∧ (s.regs 3).toNat = FvModexp.AsmDiv.recipWord (s.regs 2).toNat)
   Post := by
  intro s hpc ⟨h1, h2, hy, hx, hm⟩
  have hn := FvModexp.AsmDiv.clz_norm64 (s.regs 2).toNat hy (s.regs 2).isLt
  have hx0 := (s.regs 1).isLt
  janus_run until [entry + 0x40]
  · have hc0 : Janus.Arm64.clzNat 64 (s.regs 2).toNat = 0 := by omega
    refine entry_to_tail s _ hy hx hm h1 h2 rfl rfl ?_ ?_ rfl ?_ ?_ ?_ ?_ rfl
    all_goals simp only [setReg, Nat.reduceEqDiff, reduceIte, hc0, Nat.pow_zero, Nat.mul_one, BitVec.toNat_ofNat]
    · exact hx
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [if_neg (by omega)]
  · have hc1 : 1 ≤ Janus.Arm64.clzNat 64 (s.regs 2).toNat := by omega
    obtain ⟨c, hcd⟩ : ∃ c, c = Janus.Arm64.clzNat 64 (s.regs 2).toNat := ⟨_, rfl⟩
    rw [← hcd] at hc1 hn hbr ⊢
    have hnorm := FvModexp.AsmDiv.normalise (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat c (by omega) hn.1
      hn.2.2 hx hx0
    have hxc : (s.regs 0).toNat * 2 ^ c < 2 ^ 64 := by
      have e : ((s.regs 0).toNat + 1) * 2 ^ c ≤ (s.regs 2).toNat * 2 ^ c := Nat.mul_le_mul_right _ hx
      rw [Nat.add_mul] at e; omega
    have ea := sh_a (s.regs 0) (s.regs 1) c hc1 hn.1 hxc
    have eb := sh_b (s.regs 1) c hn.1
    have ec := sh_b (s.regs 2) c hn.1
    refine entry_to_tail s _ hy hx hm h1 h2 rfl rfl ?_ ?_ rfl ?_ ?_ ?_ ?_ rfl
    all_goals simp only [setReg, Nat.reduceEqDiff, reduceIte, ← hcd]
    · rw [ec, Nat.mod_eq_of_lt hn.2.2]
    · rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    · rw [ea, eb]; exact hnorm.1
    · rw [ea, ec, Nat.mod_eq_of_lt hn.2.2]; exact hnorm.2.1
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat (rw [if_neg (by omega)])
end FvModexp.Arm64.DivWWSum

namespace FvModexp.Arm64.DivWWSum
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open FvModexp.Lib.DivWWA64 (program entry)

/-- the standalone contract: `divWW(x1, x0, y, m)` with `y != 0`, `x1 < y`, `m` the reciprocal of `y` returns
`(q, r)` = `((x1*2^64+x0) / y, (x1*2^64+x0) % y)` and leaves memory unchanged. -/
theorem ensures (x1 x0 y m : BitVec 64) :
    Ensures program entry [x1, x0, y, m]
      (fun _ => y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧ m.toNat = FvModexp.AsmDiv.recipWord y.toNat)
      (fun s s' => results 2 s' =
          [BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) / y.toNat),
           BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem []) := by
  refine FvModexp.AsmDiv.A64.ensures_of_summary _ _ divWW_summary ?_ ?_
  · intro ret hret s hsu ⟨hy, hx, hm⟩
    have h0 : s.regs 0 = x1 := by have := hsu.args 0 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have h3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := hsu.lr
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h2]; exact hy
    · rw [h0, h2]; exact hx
    · rw [h3, h2]; exact hm
  · intro ret hret s hsu _ s' ⟨hpc, hsp, h0', h1', hr, hf⟩
    have h0 : s.regs 0 = x1 := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x0 := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    rw [h0, h1, h2] at h0' h1'
    refine ⟨⟨hsp, hr 28 (by simp), hr 29 (by simp), hr 18 (by simp)⟩, ?_, hf⟩
    simp only [results, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
    rw [← h0', ← h1']
    simp
end FvModexp.Arm64.DivWWSum
