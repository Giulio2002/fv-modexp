import FvModexp.Proofs.Arm64.ExpQ.BudClQR
import FvModexp.Proofs.Arm64.ExpQ.BudClQ8

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# TIGHT COSTS BudOK: `heven` — the closed bound of `nat.expNNEven`'s cost `IExp.clEQ` (agent infra s47)

`heven`: `IExp.clEQ 0 xl yl n ≤ 72·W + yl·(320·W)` (`W = BudQ.opC (max xl n)`; the `heven` field of expmc's
`IExp.budClQ_of`/`budClQ_of_ep`) on the spec range, CONDITIONAL on a level-generic bound of `nat.expNNPowerOfTwo`'s
cost `IExp.clP` (premise `PBound`: `clP l xl yl k ≤ 20·W + yl·160·W + 640·l` for `l ≤ 6n + 12`, `k ≤ 64n` — divmc's
after the P2 Q-form conversion; NOTES-conventions "[coordinator] 2026-11-15: TIGHT COSTS target texts — single owner").
`budClQ_ofP hP hp2 : IExp.BudClQ`.

`clEQ = ExpEven.costE …` (Exp/EvCost) = the fixed calls of expNNEven (stk.nat, make, subMod2N, the Q-form
`modularInverseModPowerOfTwo` + its reserve, the two bridged `nat.mul`) + the two inner `nat.expNN` calls, charged as
box maxima (`Exp.supU`) of `NBudE`/`NCost` over modulus length `≤ ml`, level `≤ wL3/wL4 0 ml`, `log2 ≤ 64 ml`.
* level-generic inner bounds (length `a ≤ M`, `xl ≤ M`, level `l`; `1 ≤ M ≤ 128`): `nat.rem` `≤ 4·W + 160·l`
  (`remL`), `nat.expNNSlow` `≤ makeCost xl + 8·W + yl·128·W + 160·l` (`slowL`), the Montgomery windows OBud/OCost
  `≤ 16·W + 640·l` (`oL`; `obud4L` … `ocost2L` = expmc's ExpQ/BudWinQ at level `l`);
* `inner`/`innerU`: `NBudE`/`NCost` (every branch of the path max) and their box maxima
  `≤ 20·W + yl·160·W + 32·M + 216 + 640·L`;
* the fixed part: `modinv_le` (ModInv by rounds: `sumR_le`, `rounds_le` with `log2 ml ≤ 7`; `≤ 5·W + 48·M + 208`),
  `costG_le` (subMod2N), `mul_le` (the two bridged muls, MulCostQB), the rest unfolded exactly.
-/

namespace FvModexp.Arm64.Q.BudE

open Janus Janus.Contracts FvModexp
open FvModexp.Exp (supN supU)
open FvModexp.Arm64.Q.BudW (cfB cf_le cfB_mono bs_le opC_eq amax rnd_le)

/-! ## the Montgomery windows at level `l` (copies of expmc's ExpQ/BudWinQ, level `0` → `l`, length `n ≤ M`) -/

theorem div4_leL {l n xl : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl l ≤
      cfB (l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n))
        (max xl (2 * n + 1)) n := by
  unfold ExpW4.divCost
  have t1 := cf_le (ℓ := l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) (ul := xl) hn (by omega)
  have t2 := cf_le (ℓ := l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t3 := cf_le (ℓ := l + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (ul := 2 * n + 1) hn (by omega)
  have t4 := cf_le (ℓ := l + StackNat.rnd (23 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t5 := cf_le (ℓ := l + StackNat.rnd (23 * n) + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, ?_⟩⟩
  · exact Nat.le_trans t1 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t2 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t3 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t4 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t5 (cfB_mono (by omega) (by omega))


set_option maxHeartbeats 4000000 in
/-- **window-4's budget at the top** -/
theorem obud4L {l n xl M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    ExpW4.W4Bud n xl (ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl l) l ≤ 16 * BudQ.opC M + 640 * l := by
  have hD := div4_leL (l := l) (n := n) (xl := xl) (by omega) (by omega)
  generalize ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl l = D at hD
  have hU : max xl (2 * n + 1) ≤ 2 * M + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW4.W4Bud, W4Pro.xjBud, W4Pro.xnBudA, W4Pro.xnBudAC, W4Pro.xnPre, W4Pro.xjBudA, W4Pro.xnBudAB,
    W4Pro.xnBudAA, stackNatCost, allocCost, cfB] at hD ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (l + a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    repeat' apply amax
    all_goals omega
  · rw [if_neg h40] at hDB
    repeat' apply amax
    all_goals omega

set_option maxHeartbeats 4000000 in
/-- **window-4's charged cost at the top** -/
theorem ocost4L {l n xl M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    ExpW4.W4Cost n xl (ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl l) l ≤ 16 * BudQ.opC M + 640 * l := by
  have hD := div4_leL (l := l) (n := n) (xl := xl) (by omega) (by omega)
  generalize ExpW4.divCost (divBr (NatDiv.costQ drsCQ)) n xl l = D at hD
  have hU : max xl (2 * n + 1) ≤ 2 * M + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW4.W4Cost, ExpW4.lvT, W4Pro.xjBud, W4Pro.xnBudA, W4Pro.xnBudAC, W4Pro.xnPre, W4Pro.xjBudA, W4Pro.xnBudAB,
    W4Pro.xnBudAA, stackNatCost, allocCost, cfB] at hD ⊢
  have mn := BudQ.makeCost_le16 n
  generalize makeCost n = K2 at mn ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (l + a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    omega
  · rw [if_neg h40] at hDB
    omega

/-! ## window-2 -/

theorem div2_leL {l n xl : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) :
    ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl l ≤
      cfB (l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + 2 * StackNat.rnd n + 2 * StackNat.rnd (2 * n))
        (max xl (2 * n + 1)) n := by
  unfold ExpW2.divCost
  have t1 := cf_le (ℓ := l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n) (ul := xl) hn (by omega)
  have t2 := cf_le (ℓ := l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n +
    2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t3 := cf_le (ℓ := l + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n))
    (ul := 2 * n + 1) hn (by omega)
  have t4 := cf_le (ℓ := l + StackNat.rnd (11 * n) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  have t5 := cf_le (ℓ := l + StackNat.rnd (11 * n) + 2 * StackNat.rnd (2 * n)) (ul := 2 * n + 1) hn (by omega)
  refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, ?_⟩⟩
  · exact Nat.le_trans t1 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t2 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t3 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t4 (cfB_mono (by omega) (by omega))
  · exact Nat.le_trans t5 (cfB_mono (by omega) (by omega))




set_option maxHeartbeats 4000000 in
/-- **window-2's budget at the top** -/
theorem obud2L {l n xl M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    ExpW2.W2Bud n xl (ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl l) l ≤ 16 * BudQ.opC M + 640 * l := by
  have hD := div2_leL (l := l) (n := n) (xl := xl) (by omega) (by omega)
  generalize ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl l = D at hD
  have hU : max xl (2 * n + 1) ≤ 2 * M + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW2.W2Bud, W2Pro.xjBud, W2Pro.xnBudA, W2Pro.xnBudAC, W2Pro.xnPre, W2Pro.xjBudA, W2Pro.xnBudAB,
    W2Pro.xnBudAA, stackNatCost, allocCost, cfB] at hD ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (11 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (11 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (l + a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    repeat' apply amax
    all_goals omega
  · rw [if_neg h40] at hDB
    repeat' apply amax
    all_goals omega

set_option maxHeartbeats 4000000 in
/-- **window-2's charged cost at the top** -/
theorem ocost2L {l n xl M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    ExpW2.W2Cost n xl (ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl l) l ≤ 16 * BudQ.opC M + 640 * l := by
  have hD := div2_leL (l := l) (n := n) (xl := xl) (by omega) (by omega)
  generalize ExpW2.divCost (divBr (NatDiv.costQ drsCQ)) n xl l = D at hD
  have hU : max xl (2 * n + 1) ≤ 2 * M + 1 := by omega
  have hU' : 2 * n + 1 ≤ max xl (2 * n + 1) := by omega
  rw [opC_eq]
  simp only [ExpW2.W2Cost, ExpW2.lvT, W2Pro.xjBud, W2Pro.xnBudA, W2Pro.xnBudAC, W2Pro.xnPre, W2Pro.xjBudA, W2Pro.xnBudAB,
    W2Pro.xnBudAA, stackNatCost, allocCost, cfB] at hD ⊢
  have mn := BudQ.makeCost_le16 n
  generalize makeCost n = K2 at mn ⊢
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (11 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize max xl (2 * n + 1) = U at hD hU hU'
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (11 * n) = a at r1 hD ⊢
  generalize StackNat.rnd (xl - n + 1) = b at r2 hD ⊢
  generalize StackNat.rnd n = c at r3 hD ⊢
  generalize StackNat.rnd (2 * n) = d at r4 hD ⊢
  have hDB : D ≤ 2592 * U + 16 * (U - n) + 160 * (l + a + b + 2 * c + 2 * d) + 11016 +
      (if n < 40 then 0 else 560 * U + 88 * n + 1960) := hD
  clear hD
  by_cases h40 : n < 40
  · rw [if_pos h40] at hDB
    omega
  · rw [if_neg h40] at hDB
    omega


/-- **the windows at level `l`** (`OBud`, `OCost` of the bridged division) -/
theorem oL {l n xl yl M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    ExpOdd.OBud (divBr (NatDiv.costQ drsCQ)) n xl yl l ≤ 16 * BudQ.opC M + 640 * l ∧
    ExpOdd.OCost (divBr (NatDiv.costQ drsCQ)) n xl yl l ≤ 16 * BudQ.opC M + 640 * l := by
  unfold ExpOdd.OBud ExpOdd.OCost
  split
  · exact ⟨obud4L hnM hxM hM hM1, ocost4L hnM hxM hM hM1⟩
  · exact ⟨obud2L hnM hxM hM hM1, ocost2L hnM hxM hM hM1⟩

/-! ## `nat.rem` and `nat.expNNSlow` at level `l` (length `a ≤ M`) -/

/-- the bridged `nat.rem` (`IExp.clRQ l xl a`) -/
theorem remL {l xl a M : Nat} (hx : xl ≤ M) (ha : a ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    Q.brC (Q.NatDiv.costQ Q.drsCQ) NatRem.need l xl a ≤ 4 * BudQ.opC M + 160 * l := by
  have hm1 := BudQ.makeCost_le16 xl
  have hm2 := BudQ.makeCost_le16 (xl + 1)
  have hm3 := BudQ.makeCost_le16 (xl - a + 1)
  have hm4 : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
  have hd : drsCQ (xl + 1) a ≤ (if a < 40 then 0 else 560 * (xl + 1) + 88 * a + 1400) := by
    split
    · rw [drsCQ_small (by assumption)]; exact Nat.le_refl _
    · exact drsCQ_le (by omega) (by omega)
  simp only [Q.brC, Q.NatDiv.costQ, Q.DivLarge.costQ, NatRem.need, stkRes, capB, potK, BudQ.opC, allocCost]
  split at hd <;> omega

/-- the bridged Q-form `nat.expNNSlow` (`IExp.clSQ l xl yl a`) -/
theorem slowL {l xl yl a M : Nat} (hx : xl ≤ M) (ha : a ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH l xl yl a ≤
      makeCost xl + 8 * BudQ.opC M + yl * (128 * BudQ.opC M) + 160 * l := by
  simp only [slowBr, ExpSlow.costQ, ExpSlow.needH]
  have hS := Nat.le_trans (Exp.supN_mono sqrCQ (show max xl a ≤ M by omega)) (ExpSlow.sq_le hM)
  have hMu := Nat.le_trans (Exp.supN_mono (fun j => mulCQ j xl) (show 2 * max xl a ≤ 2 * M by omega))
    (ExpSlow.mul_le hM hx)
  have hD := Nat.le_trans (Exp.supN_mono (fun j => NatDiv.costQ drsCQ j a) (show 3 * max xl a ≤ 3 * M by omega))
    (ExpSlow.div_le hM ha)
  rw [opC_eq]
  have hr : stkRes (l + (48 * max xl a + 64)) = 160 * l + 7680 * max xl a + 10680 := by
    unfold stkRes capB potK; omega
  rw [hr]
  have hxa : max xl a ≤ M := by omega
  generalize supN sqrCQ (max xl a) = s1 at hS ⊢
  generalize supN (fun j => mulCQ j xl) (2 * max xl a) = s2 at hMu ⊢
  generalize supN (fun j => NatDiv.costQ drsCQ j a) (3 * max xl a) = s3 at hD ⊢
  generalize max xl a = A at hxa ⊢
  have hsum : s1 + s2 + s3 ≤ 2 * (2048 * M + 2072) := by
    by_cases h40 : a < 40
    · rw [if_pos h40] at hD; omega
    · rw [if_neg h40] at hD; omega
  have hm : 64 * yl * (s1 + s2 + s3) ≤ yl * (128 * (2048 * M + 2072)) := by
    rw [Nat.mul_comm 64 yl, Nat.mul_assoc]; exact Nat.mul_le_mul_left yl (by omega)
  omega

/-! ## the inner `nat.expNN` calls -/

/-- the box maximum is below any bound of the box -/
theorem supU_le (f : Nat → Nat → Nat → Nat → Nat → Nat) (x y a l k B : Nat)
    (h : ∀ a0 l0 k0, a0 ≤ a → l0 ≤ l → k0 ≤ k → f x y a0 l0 k0 ≤ B) : supU f x y a l k ≤ B := by
  unfold supU
  exact ExpSlow.supN_le_const _ _ a fun a0 ha => ExpSlow.supN_le_const _ _ l fun l0 hl =>
    ExpSlow.supN_le_const _ _ k fun k0 hk => h a0 l0 k0 ha hl hk

/-- **the premise** (divmc, after the P2 Q-form conversion): a LEVEL-GENERIC bound of `nat.expNNPowerOfTwo`'s cost
`IExp.clP` at the levels `l ≤ 6·n + 12` (`≥ wL4 0 n`) where `expNNEven`'s inner `nat.expNN` calls run it, `log2 m = k ≤
64·n`; `W = BudQ.opC (max xl n)`. (`hp2` of `IExp.budClQ_of` is its tighter `l = 0` sibling.) -/
def PBound : Prop :=
  ∀ l xl yl n k, l ≤ 6 * n + 12 → xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → k ≤ 64 * n →
    IExp.clP l xl yl k ≤ 20 * BudQ.opC (max xl n) + yl * (160 * BudQ.opC (max xl n)) + 640 * l

/-- one inner `nat.expNN` call (modulus length `a ≤ n`, level `l`, `log2 m = k`): budget and charged cost, every branch of
the path max -/
theorem inner (hP : PBound) {xl yl n a l k : Nat} (hx : xl ≤ 128) (hy : yl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128)
    (ha : a ≤ n) (hl : l ≤ 6 * n + 12) (hk : k ≤ 64 * n) :
    ExpEven.NBudE IExp.clFQ IExp.clRQ IExp.clSQ IExp.clP xl yl a l k ≤
        20 * BudQ.opC (max xl n) + yl * (160 * BudQ.opC (max xl n)) + 32 * max xl n + 216 + 640 * l ∧
    ExpN.NCost IExp.clFQ IExp.clRQ IExp.clSQ IExp.clP xl yl a l k ≤
        20 * BudQ.opC (max xl n) + yl * (160 * BudQ.opC (max xl n)) + 32 * max xl n + 216 + 640 * l := by
  have hM : max xl n ≤ 128 := by omega
  have hR := remL (l := l) (xl := xl) (a := a) (Nat.le_max_left xl n) (by omega) hM (by omega)
  have hS := slowL (l := l) (xl := xl) (yl := yl) (a := a) (Nat.le_max_left xl n) (by omega) hM (by omega)
  have hPP := hP l xl yl n k hl hx hy hn0 hn hk
  have hO := oL (l := l) (n := a) (xl := xl) (yl := yl) (M := max xl n) (by omega) (Nat.le_max_left xl n) hM (by omega)
  have m1 : makeCost 1 = 40 := by decide
  have ma := BudQ.makeCost_le16 a; have mx := BudQ.makeCost_le16 xl
  have hYS : yl * (128 * BudQ.opC (max xl n)) ≤ yl * (160 * BudQ.opC (max xl n)) :=
    Nat.mul_le_mul_left yl (Nat.mul_le_mul_right _ (by decide))
  simp only [ExpEven.NBudE, ExpN.NCost, IExp.clFQ, IExp.clRQ, IExp.clSQ] at hS hR hO ⊢
  have hxM := Nat.le_max_left xl n
  have hnM := Nat.le_max_right xl n
  generalize BudQ.opC (max xl n) = W at hR hS hPP hO hYS ⊢
  generalize max xl n = M at hR hS hPP hO hYS hM hxM hnM ⊢
  generalize yl * (160 * W) = Y at hPP hYS ⊢
  generalize yl * (128 * W) = Y' at hS hYS
  obtain ⟨hO1, hO2⟩ := hO
  constructor <;> omega

/-- both inner calls' box maxima (level box `L ≤ 6·n + 12`) -/
theorem innerU (hP : PBound) {xl yl n L : Nat} (hx : xl ≤ 128) (hy : yl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128)
    (hL : L ≤ 6 * n + 12) :
    IExp.clBUQ xl yl n L (64 * n) ≤
        20 * BudQ.opC (max xl n) + yl * (160 * BudQ.opC (max xl n)) + 32 * max xl n + 216 + 640 * L ∧
    IExp.clCUQ xl yl n L (64 * n) ≤
        20 * BudQ.opC (max xl n) + yl * (160 * BudQ.opC (max xl n)) + 32 * max xl n + 216 + 640 * L := by
  constructor
  · exact supU_le _ _ _ _ _ _ _ fun a0 l0 k0 ha hl hk =>
      Nat.le_trans (inner hP hx hy hn0 hn ha (by omega) hk).1 (by omega)
  · exact supU_le _ _ _ _ _ _ _ fun a0 l0 k0 ha hl hk =>
      Nat.le_trans (inner hP hx hy hn0 hn ha (by omega) hk).2 (by omega)


/-! ## the fixed part: `modularInverseModPowerOfTwo` (Q-form, by rounds), `subMod2N`, the two bridged `nat.mul` -/

theorem sqr_le {z : Nat} (hz : z < 158) : sqrCQ z ≤ 128 * z + 808 := by
  have := sqrCQ_le_B (n := z) (by omega); unfold sqrCB at this
  split at this <;> (try split at this) <;> omega

theorem mul_le {a c M : Nat} (ha : a ≤ M) (hc : c ≤ M) (hM : M ≤ 128) : mulCQ a c ≤ 937 * M + 3968 := by
  have := mulCQ_le_B (xl := a) (yl := c) (by omega)
  have h1 : max a c ≤ M := by omega
  have h2 : min a c ≤ M := by omega
  generalize max a c = u at this h1; generalize min a c = v at this h2
  unfold mulCB at this; split at this
  · omega
  · split at this <;> omega

/-- one Hensel round of `ModInv` (also the final round) at `xl := ml`, `n := 64·ml` -/
theorem rc_le {ml M z k : Nat} (hml : ml ≤ M) (hM : M ≤ 128) (hz : z ≤ ml + 1) (hk : k ≤ ml) :
    sqrCQ z + mulCQ k (min k ml) + 2 * makeCost (2 * ModInv.NW (64 * ml) + 2) + makeCost (ModInv.NW (64 * ml) + 2) +
      SubMod2N.cost (64 * ml) ≤ 1225 * M + 5784 := by
  have h1 := sqr_le (z := z) (by omega)
  have h2 := mul_le (a := k) (c := min k ml) (M := M) (by omega) (by omega) hM
  have m1 := BudQ.makeCost_le16 (2 * ModInv.NW (64 * ml) + 2)
  have m2 := BudQ.makeCost_le16 (ModInv.NW (64 * ml) + 2)
  simp only [ModInv.NW, SubMod2N.cost, SubMod2N.wCost, SubMod2N.W, allocCost] at m1 m2 ⊢
  omega

theorem sumR_le {ml M : Nat} (hml : ml ≤ M) (hM : M ≤ 128) :
    ∀ r, 2 ^ r ≤ ml → ModInv.sumR sqrCQ mulCQ ml (64 * ml) r ≤ r * (1225 * M + 5784) := by
  intro r
  induction r with
  | zero => intro _; exact Nat.zero_le _
  | succ r ih =>
    intro h
    have hp : 2 ^ r ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : ModInv.zB (64 * ml) (r + 1) ≤ ml + 1 := by
      unfold ModInv.zB; split
      · unfold ModInv.NW; omega
      · rw [Nat.add_sub_cancel]; omega
    rw [ModInv.sumR_succ, Nat.add_mul r 1, Nat.one_mul]
    have := rc_le (ml := ml) (k := 2 ^ (r + 1)) hml hM hz h
    have := ih (by omega)
    simp only [ModInv.roundCost]
    omega

theorem rounds_le {r M : Nat} (hr : r ≤ 7) (hp : 2 ^ r ≤ M) :
    r * (1225 * M + 5784) + (1225 * M + 5784) ≤ 5 * (2048 * M + 2072) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> subst h <;> simp only [Nat.reducePow] at hp <;> omega

/-- **`ModInv`'s Q-form cost** at `xl := ml`, `n := 64·ml` (`log2 ml + 1` rounds at sizes `≤ ml + 1`) -/
theorem modinv_le {ml M : Nat} (h1 : 1 ≤ ml) (hml : ml ≤ M) (hM : M ≤ 128) :
    ModInv.cost sqrCQ mulCQ ml (64 * ml) ≤ 5 * (2048 * M + 2072) + 48 * M + 208 := by
  have hNW : ModInv.NW (64 * ml) = ml := by unfold ModInv.NW; omega
  have hs := sumR_le hml hM (Nat.log2 ml) (Nat.log2_self_le (by omega))
  have hfin := rc_le (ml := ml) (z := ml + 1) (k := ml) hml hM (Nat.le_refl _) (Nat.le_refl _)
  have hr7 : Nat.log2 ml < 8 := (Nat.log2_lt (by omega)).2 (by simp only [Nat.reducePow]; omega)
  have hp : 2 ^ Nat.log2 ml ≤ M := Nat.le_trans (Nat.log2_self_le (by omega)) hml
  have hR := rounds_le (r := Nat.log2 ml) (M := M) (by omega) hp
  have m1 := BudQ.makeCost_le16 (ml + 1); have m2 := BudQ.makeCost_le16 (2 * ml)
  simp only [ModInv.cost]
  rw [hNW] at hfin ⊢
  generalize Nat.log2 ml = r at hs hR
  omega

/-- `subMod2N`'s general budget at `n = 64·ml` (`ml` words; `ml` growslices of `≤ 2·ml + 2` words) -/
theorem costG_le {ml : Nat} (hml : ml ≤ 128) : SubMod2N.costG (64 * ml) ≤ 4232 * ml + 520 := by
  have hW : SubMod2N.W (64 * ml) = ml := by unfold SubMod2N.W; omega
  simp only [SubMod2N.costG, SubMod2N.gA, SubMod2N.cost, SubMod2N.wCost, hW, allocCost]
  have : ml * (2 * (8 * (2 * ml + 2)) + 24) ≤ ml * (2 * (8 * (2 * 128 + 2)) + 24) :=
    Nat.mul_le_mul_left ml (by omega)
  omega

/-! ## `heven` -/

/-- **`heven`** (the `even` field of expmc's `IExp.budClQ_of`), conditional on divmc's level-generic P bound `PBound` -/
theorem heven (hP : PBound) : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
    IExp.clEQ 0 xl yl n ≤ 72 * BudQ.opC (max xl n) + yl * (320 * BudQ.opC (max xl n)) := by
  intro xl yl n hx hy hn0 hn
  have hL3 : ExpEven.wL3 0 n ≤ 6 * n + 12 := by simp only [ExpEven.wL3, ExpEven.wL2, StackNat.rnd]; omega
  have hL4 : ExpEven.wL4 0 n ≤ 6 * n + 12 := by simp only [ExpEven.wL4, ExpEven.wL3, ExpEven.wL2, StackNat.rnd]; omega
  have hC1 := (innerU hP hx hy hn0 hn hL3).2
  obtain ⟨hB2, hC2⟩ := innerU hP hx hy hn0 hn hL4
  have hM : max xl n ≤ 128 := by omega
  have hnM := Nat.le_max_right xl n
  have hMI := modinv_le (ml := n) (M := max xl n) hn0 hnM hM
  have hMu := mul_le (a := n) (c := n) (M := max xl n) hnM hnM hM
  have hG := costG_le hn
  simp only [IExp.clEQ, ExpEven.costE, ExpEven.eC1, ExpEven.eC2]
  generalize IExp.clBUQ xl yl n (ExpEven.wL4 0 n) (64 * n) = B2 at hB2 ⊢
  generalize IExp.clCUQ xl yl n (ExpEven.wL3 0 n) (64 * n) = C1 at hC1 ⊢
  generalize IExp.clCUQ xl yl n (ExpEven.wL4 0 n) (64 * n) = C2 at hC2 ⊢
  generalize ModInv.cost sqrCQ mulCQ n (64 * n) = MI at hMI ⊢
  generalize SubMod2N.costG (64 * n) = G at hG ⊢
  simp only [ExpEven.mulBrE, Q.brC]
  generalize mulCQ n n = MU at hMu ⊢
  have e1 : yl * (160 * BudQ.opC (max xl n)) = 160 * (yl * BudQ.opC (max xl n)) := Nat.mul_left_comm _ _ _
  have e2 : yl * (320 * BudQ.opC (max xl n)) = 320 * (yl * BudQ.opC (max xl n)) := Nat.mul_left_comm _ _ _
  rw [e1] at hB2 hC1 hC2; rw [e2]
  generalize yl * BudQ.opC (max xl n) = Y at hB2 hC1 hC2 ⊢
  have hW := opC_eq (max xl n)
  generalize BudQ.opC (max xl n) = W at hB2 hC1 hC2 hW ⊢
  generalize max xl n = M at hB2 hC1 hC2 hW hMI hMu hM hnM ⊢
  simp only [ExpEven.mulBrE, Q.brC, stkRes_eq, ModInv.D, ModInv.NW, stackNatCost, makeB, allocCost,
    ExpEven.wL4, ExpEven.wL3, ExpEven.wL2, StackNat.rnd] at hB2 hC1 hC2 ⊢
  omega

/-- `IExp.BudClQ` from divmc's `PBound` and `hp2` (expmc's `IExp.budClQ_of_ep`: rem = divmc's `Q.BudT.rem`,
slow/obud/ocost = expmc's; `heven` discharged here) -/
theorem budClQ_ofP (hP : PBound)
    (hp2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      IExp.clP 0 xl yl lm ≤ 6 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n))) : IExp.BudClQ :=
  IExp.budClQ_of_ep (heven hP) hp2

/-- **TIGHT COSTS: `IExp.BudClQ` CLOSED (arm64)** — `heven` (this module) on divmc's `Q.BudP2.pBound`, through
`IExp.budClQ_of_e` (ExpQ/BudClQ8: P target 8 W) -/
theorem budClQ : IExp.BudClQ := IExp.budClQ_of_e (heven Q.BudP2.pBound)

end FvModexp.Arm64.Q.BudE
