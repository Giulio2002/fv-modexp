import FvModexp.Proofs.Amd64.Exp.P2DDefs
import FvModexp.Proofs.Amd64.Exp.P2W2C
import FvModexp.Proofs.Amd64.Exp.P2W4C
import FvModexp.Proofs.Common.MulCostQB
import FvModexp.Proofs.Common.BudQ

set_option autoImplicit false

/-!
# TIGHT COSTS: closed bounds of `nat.expNNPowerOfTwo`'s cost (amd64; agent expmc s83, copy of arm64 ExpQ/BudP2Q, divmc s42)

`P2D.costP P2W2.costB P2W4.costB` (= `EvenRow.cP`; the windows' bridged costs `P2W2.costB` /
`P2W4.costB` = the Q-form cost + ONE stack reserve `stkRes (HW ℓ lm)`) at stack level `ℓ`, base length `xl`, exponent
length `yl`, `log2 m = k ≤ 64 n` (`n ≤ 128` the modulus words), `W = BudQ.opC (max xl n)`:
* `cP_le`: `cP sqrCQ mulCQ ℓ xl yl k ≤ 8 W + yl·64 W + 160 ℓ` (level slope = the reserve's `stkRes` slope);
* `hp2Q` (the `ℓ = 0`, `k < 64 n` field) and `pBound` (infra's `PBound` text `20 W + yl·160 W + 640 ℓ`).
Per-operation closed bounds: divmc's `sqrCQ_le_B`, `MCQ_P0` / `box1` / `mulCQ_le_box` (Common/MulCostQB);
`makeCost_le16`; `stkRes_eq`. Real mirror of exactly these definitions: scratchpad s42/p2q.py (setup ≤ 5.8 W,
per y-word ≤ 7.9 W at the exact op costs; ≤ 6.35 W / 14.3 W with the closed op bounds used here).
-/

namespace FvModexp.Amd64.Q.BudP2

open FvModexp

theorem supTo_le {f : Nat → Nat} {B : Nat} : ∀ n, (∀ j, j ≤ n → f j ≤ B) → P2D.supTo f n ≤ B
  | 0, h => h 0 (Nat.le_refl _)
  | n + 1, h => by
    simp only [P2D.supTo]
    exact Nat.max_le.2 ⟨supTo_le n (fun j hj => h j (by omega)), h _ (Nat.le_refl _)⟩

/-- the closed per-operation bounds at `w ≤ 128` words -/
theorem ops (w : Nat) (hw : w ≤ 128) :
    (w < 40 → sqrCQ w ≤ 32 * w + 88 ∧ mulCQ w w ≤ 32 * w + 88) ∧
      (w < 79 → sqrCQ w ≤ 32 * w + 88 ∧ mulCQ w w ≤ 160 * w + 1032) ∧
      (sqrCQ w ≤ 128 * w + 808 ∧ mulCQ w w ≤ 538 * w + 4912) := by
  have hS := sqrCQ_le_B (n := w) (by omega)
  unfold sqrCB at hS
  refine ⟨fun h => ⟨by rw [if_pos (by omega)] at hS; exact hS, ?_⟩, fun h => ⟨by rw [if_pos (by omega)] at hS; exact hS,
    mulCQ_le_box1 (Nat.le_refl _) (Nat.le_refl _) h⟩, ?_, mulCQ_le_box (Nat.le_refl _) (Nat.le_refl _) (by omega)⟩
  · have := MCQ_P0 w w h; unfold mulCQ; rw [Nat.max_self, Nat.min_self]; omega
  · split at hS
    · omega
    · rw [if_pos (by omega)] at hS; exact hS

/-- `32 · min yl q · c ≤ yl · B` from `32 · c ≤ B` (the per-word term) -/
theorem yterm {yl q c B k : Nat} (h : k * c ≤ B) : k * min yl q * c ≤ yl * B := by
  calc k * min yl q * c = min yl q * (k * c) := by rw [Nat.mul_comm k, Nat.mul_assoc]
    _ ≤ yl * B := Nat.mul_le_mul (Nat.min_le_left _ _) h

set_option maxHeartbeats 4000000 in
/-- **window 2**: its bridged cost plus the `costO`/`costP` extras (`40 + 32 M + 240`) within `8 W + yl·64 W + 160 ℓ` -/
theorem w2_le {ℓ yl j M W : Nat} (hw : (j + 63) / 64 ≤ M) (hM : M ≤ 128) (hWd : W = 2048 * M + 2072) :
    P2W2.costB ℓ yl j + 40 + (32 * M + 240) ≤ 8 * W + yl * (64 * W) + 160 * ℓ := by
  simp only [P2W2.costB, P2W2.cost, P2W2.cost0, P2W2.bc, P2Pre.cost, P2Pre.rc, P2Pre.tC, P2W2.HW,
    P2Pre.NB, P2Pre.W, P2W2.W, stkRes_eq, StackNat.rnd]
  generalize hwd : (j + 63) / 64 = w at hw ⊢
  obtain ⟨o1, o2, o3⟩ := ops w (by omega)
  have hT := BudQ.makeCost_le16 (w + 4)
  have ha : allocCost 8 = 40 := by simp only [allocCost]
  rw [ha]
  generalize sqrCQ w = S at o1 o2 o3 ⊢
  generalize mulCQ w w = Mu at o1 o2 o3 ⊢
  generalize makeCost (w + 4) = T at hT ⊢
  rcases Nat.lt_or_ge w 40 with h40 | h40
  · have := o1 h40
    have hbc : 32 * (2 * S + Mu + 3 * T) ≤ 64 * W := by omega
    have hy := yterm (yl := yl) (q := (j - 2) / 64 + 1) hbc
    omega
  rcases Nat.lt_or_ge w 79 with h79 | h79
  · have := o2 h79
    have hbc : 32 * (2 * S + Mu + 3 * T) ≤ 64 * W := by omega
    have hy := yterm (yl := yl) (q := (j - 2) / 64 + 1) hbc
    omega
  · have := o3
    have hbc : 32 * (2 * S + Mu + 3 * T) ≤ 64 * W := by omega
    have hy := yterm (yl := yl) (q := (j - 2) / 64 + 1) hbc
    omega

set_option maxHeartbeats 4000000 in
/-- **window 4** (as `w2_le`) -/
theorem w4_le {ℓ yl j M W : Nat} (hw : (j + 63) / 64 ≤ M) (hM : M ≤ 128) (hWd : W = 2048 * M + 2072) :
    P2W4.costB ℓ yl j + 40 + (32 * M + 240) ≤ 8 * W + yl * (64 * W) + 160 * ℓ := by
  simp only [P2W4.costB, P2W4.cost, P2W4.cost0, P2W4.bc, P2Pre.cost, P2Pre.rc, P2Pre.tC, P2W4.HW,
    P2Pre.NB, P2Pre.W, P2W4.W, stkRes_eq, StackNat.rnd]
  generalize hwd : (j + 63) / 64 = w at hw ⊢
  obtain ⟨o1, o2, o3⟩ := ops w (by omega)
  have hT := BudQ.makeCost_le16 (w + 4)
  have ha : allocCost 8 = 40 := by simp only [allocCost]
  rw [ha]
  generalize sqrCQ w = S at o1 o2 o3 ⊢
  generalize mulCQ w w = Mu at o1 o2 o3 ⊢
  generalize makeCost (w + 4) = T at hT ⊢
  rcases Nat.lt_or_ge w 40 with h40 | h40
  · have := o1 h40
    have hbc : 16 * (4 * S + Mu + 5 * T) ≤ 64 * W := by omega
    have hy := yterm (yl := yl) (q := (j - 2) / 64 + 1) hbc
    omega
  rcases Nat.lt_or_ge w 79 with h79 | h79
  · have := o2 h79
    have hbc : 16 * (4 * S + Mu + 5 * T) ≤ 64 * W := by omega
    have hy := yterm (yl := yl) (q := (j - 2) / 64 + 1) hbc
    omega
  · have := o3
    have hbc : 16 * (4 * S + Mu + 5 * T) ≤ 64 * W := by omega
    have hy := yterm (yl := yl) (q := (j - 2) / 64 + 1) hbc
    omega

/-- one exponent-length's path max (`costO`) plus the `costP` extras -/
theorem costO_le {ℓ yl j M W : Nat} (hw : (j + 63) / 64 ≤ M) (hM : M ≤ 128) (hWd : W = 2048 * M + 2072) :
    P2D.costO (P2W2.costB) (P2W4.costB) ℓ yl j + (32 * M + 240) ≤
      8 * W + yl * (64 * W) + 160 * ℓ := by
  have h2 := w2_le (ℓ := ℓ) (yl := yl) hw hM hWd
  have h4 := w4_le (ℓ := ℓ) (yl := yl) hw hM hWd
  unfold P2D.costO
  generalize P2W2.costB ℓ yl j = A at h2 ⊢
  generalize P2W4.costB ℓ yl j = B at h4 ⊢
  have ha : allocCost 8 = 40 := by simp only [allocCost]
  rw [ha]
  generalize yl * (64 * W) = Y at h2 h4 ⊢
  omega

/-- **the level-generic closed bound** of `expNNPowerOfTwo`'s Q-form cost -/
theorem cP_le {ℓ xl yl n k : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) (hk : k ≤ 64 * n) :
    P2D.costP P2W2.costB P2W4.costB ℓ xl yl k ≤
      8 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n)) + 160 * ℓ := by
  have hW : BudQ.opC (max xl n) = 2048 * max xl n + 2072 := by unfold BudQ.opC allocCost; omega
  generalize BudQ.opC (max xl n) = W at hW ⊢
  have hM : max xl n ≤ 128 := by omega
  have hS : P2D.supTo (P2D.costO (P2W2.costB) (P2W4.costB) ℓ yl) k ≤
      8 * W + yl * (64 * W) + 160 * ℓ - (32 * max xl n + 240) :=
    supTo_le (f := P2D.costO (P2W2.costB) (P2W4.costB) ℓ yl) k
      (fun j hj => by
        have h := costO_le (ℓ := ℓ) (yl := yl) (j := j) (M := max xl n) (W := W) (by omega) hM hW
        omega)
  have h0 := costO_le (ℓ := ℓ) (yl := yl) (j := 0) (M := max xl n) (W := W) (by omega) hM hW
  have m1 := BudQ.makeCost_le16 (xl + 2)
  have m2 := BudQ.makeCost_le16 (k / 64 + 2)
  simp only [P2D.costP]
  omega

/-- **`hp2`** (the `p2` field of `IExp.budClQ_of`, P target raised to `8 W`: NOTES-conventions "[divmc s42]") -/
theorem hp2Q : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    P2D.costP P2W2.costB P2W4.costB 0 xl yl lm ≤ 8 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n)) := by
  intro xl yl n lm hx _ hn0 hn hlm
  have := cP_le (ℓ := 0) (yl := yl) hx hn0 hn (Nat.le_of_lt hlm)
  omega

/-- **infra's `PBound`** (ExpQ/BudEvenQ, text `20 W + yl·160 W + 640 l`, `l ≤ 6 n + 12`, `k ≤ 64 n`) -/
theorem pBound : ∀ l xl yl n k, l ≤ 6 * n + 12 → xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → k ≤ 64 * n →
    P2D.costP P2W2.costB P2W4.costB l xl yl k ≤ 20 * BudQ.opC (max xl n) + yl * (160 * BudQ.opC (max xl n)) + 640 * l := by
  intro l xl yl n k _ hx _ hn0 hn hk
  have h := cP_le (ℓ := l) (yl := yl) hx hn0 hn hk
  have e : yl * (64 * BudQ.opC (max xl n)) ≤ yl * (160 * BudQ.opC (max xl n)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide))
  omega

end FvModexp.Amd64.Q.BudP2
