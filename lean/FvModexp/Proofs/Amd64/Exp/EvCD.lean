import FvModexp.Proofs.Amd64.Exp.DivInst
import FvModexp.Proofs.Common.BudQ
import FvModexp.Proofs.Common.MulCostQB

set_option autoImplicit false

/-!
# amd64 `nat.expNNEven`: a LEVEL-DEPENDENT bound on the closed `nat.div` cost (asm s72)

The even path's two inner `nat.expNN` calls need `costF l a n ≤ costD` (`ExpOdd.OBud`) at the window levels they reach.
A constant `costD` valid for every level `≤ 2^16` is `≥ stkRes (2^16 + …) ≈ 1.1·10^7 > 2^22`, more than the toy
runtime's whole budget (`64 · b ≤ HSIZE`), so the even row's witness could not exist. Instead the bound is taken at
the CALL's level `L` and the call's own lengths: `cD K L A n = CQB A n + stkRes (L + K + 16 · A + 64)` dominates
`DivInst.divC l a n` for every level `l ≤ L + K`, dividend length `a ≤ A ≤ 257`, divisor length `n ≤ 128`
(`divC_le`). `CQB A n` bounds the level-free part
`Q.NatDiv.costQ Q.drsCQ a n` (two `divRecursiveStep` recursion levels, as divmc's `Q.BudM.drsCQ_le` for `ul ≤ 129`,
here `ul ≤ 258`: at most 11 steps per level).
-/

open FvModexp FvModexp.BudQ

namespace FvModexp.Amd64.ExpEven

/-- (as divmc's private `Q.BudM.mul_small`) -/
theorem mulS {a b : Nat} (ha : a ≤ 33) (hb : b ≤ 31) : mulCQ a b ≤ 1112 := by
  have h := mulCQ_le_B (xl := a) (yl := b) (by omega)
  unfold mulCB at h; split at h <;> omega

/-- (as divmc's private `Q.BudM.mul_mid`) -/
theorem mulM {a b : Nat} (ha : a ≤ 65) (hb : b ≤ 63) : mulCQ a b ≤ 22138 := by
  have h := mulCQ_le_B (xl := a) (yl := b) (by omega)
  unfold mulCB at h; split at h
  · omega
  · split at h <;> omega

theorem steps11 {ul n : Nat} (hu : ul ≤ 258) (hn : ¬ n < 40) : (ul - n) / (n / 2) + 1 ≤ 11 := by
  have : (ul - n) / (n / 2) < 11 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  omega

theorem drsCQ_le1 {ul n : Nat} (hu : ul ≤ 258) (hn : n ≤ 65) : Q.drsCQ ul n ≤ 11 * 1112 := by
  by_cases h40 : n < 40
  · rw [Q.drsCQ_small h40]; exact Nat.zero_le _
  · rw [Q.drsCQ_big h40, Q.drsCQ_small (by omega), Nat.zero_add]
    exact Nat.mul_le_mul (steps11 hu h40) (mulS (by omega) (by omega))

/-- `drsCQ ul n ≤ 11 · (11 · 1112 + 22138)` for `ul ≤ 258`, `n ≤ 128` -/
theorem drsCQ_le {ul n : Nat} (hu : ul ≤ 258) (hn : n ≤ 128) : Q.drsCQ ul n ≤ 11 * (11 * 1112 + 22138) := by
  by_cases h40 : n < 40
  · rw [Q.drsCQ_small h40]; exact Nat.zero_le _
  · rw [Q.drsCQ_big h40]
    exact Nat.mul_le_mul (steps11 hu h40)
      (Nat.add_le_add (drsCQ_le1 hu (by omega)) (mulM (by omega) (by omega)))

/-- the level-free part of the closed `nat.div` cost for dividends `≤ A` words and an `n`-word divisor -/
def CQB (A n : Nat) : Nat := 3 * (16 * A + 104) + 40 + (if n < 40 then 0 else 11 * (11 * 1112 + 22138))

/-- **the level-dependent division bound**: levels `≤ L + K`, dividends `≤ A` words, divisor `n` words -/
def cD (K L A n : Nat) : Nat := CQB A n + stkRes (L + K + 16 * A + 64)

theorem costQ_le {a A n : Nat} (ha : a ≤ A) (hA : A ≤ 257) (hn : n ≤ 128) :
    Q.NatDiv.costQ Q.drsCQ a n ≤ CQB A n := by
  have h1 := makeCost_le16 a
  have h2 := makeCost_le16 (a + 1)
  have h3 := makeCost_le16 (a - n + 1)
  have h4 : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
  have h5 : Q.drsCQ (a + 1) n ≤ (if n < 40 then 0 else 11 * (11 * 1112 + 22138)) := by
    split
    · rw [Q.drsCQ_small (by assumption)]; exact Nat.le_refl _
    · exact drsCQ_le (by omega) hn
  simp only [Q.NatDiv.costQ, Q.DivLarge.costQ, CQB]
  by_cases hn40 : n < 40 <;> simp only [hn40, if_true, if_false] at h5 ⊢ <;> omega

/-- **`DivInst.divC l a n ≤ cD K L A n`** for `l ≤ L + K`, `a ≤ A ≤ 257`, `n ≤ 128` -/
theorem divC_le (K : Nat) : ∀ L A l a n, l ≤ L + K → a ≤ A → A ≤ 257 → n ≤ 128 →
    DivInst.divC l a n ≤ cD K L A n := by
  intro L A l a n hl ha hA hn
  have h := costQ_le ha hA hn
  simp only [DivInst.divC, DivInst.divBr, cD, stkRes, capB, potK]
  omega

/-- `cD K` is monotone in the level and the dividend bound -/
theorem cD_mono (K : Nat) {L L' A A' n : Nat} (h : L ≤ L') (hA : A ≤ A') : cD K L A n ≤ cD K L' A' n := by
  simp only [cD, CQB, stkRes, capB, potK]; split <;> omega

end FvModexp.Amd64.ExpEven
