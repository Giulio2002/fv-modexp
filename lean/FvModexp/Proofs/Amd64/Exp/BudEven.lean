import FvModexp.Proofs.Amd64.Exp.BudWin
import FvModexp.Proofs.Amd64.Exp.BudP2
import FvModexp.Proofs.Amd64.Exp.BudSlow
import FvModexp.Proofs.Amd64.Exp.EvCost
import FvModexp.Proofs.Amd64.Exp.EvCD
import FvModexp.Proofs.Amd64.Exp.RemInst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# TIGHT COSTS (amd64): `heven` — the closed bound of `nat.expNNEven`'s cost at the top (agent expmc s84; twin of arm64
ExpQ/BudEvenQ, infra s47)

`heven`: `EvenRow.cE 0 xl yl n ≤ 120·W + yl·(256·W)` (`W = BudQ.opC (max xl n)`) on the spec range — `IExp.EvenT`.
Stated on the unfolded cost (`ExpEven.costE` of the two box maxima at the level-dependent division bound
`cD (needO x a) l (max (2a+1) x) a` = EvInst's `cDE`), so this module does not import the instance modules.
* the division bound at the inner levels `l ≤ 6M + 12`: `cD_le` `≤ 16·W`;
* the Montgomery windows at level `l` for ANY division bound `D` (amd64 charges one `costD` per division): window
  demand `ODem` and charged cost `OCost` `≤ 2·D + 6·W` (`odem`, `ocostL`);
* `nat.rem` (`remL`, `≤ 8·W + 160·l`), `nat.expNNSlow` (`slowL`), `nat.expNNPowerOfTwo` (BudP2 `cP_le`) at level `l`;
* `inner`/`innerU`: `NBudO`/`NCost` (all branches) and their box maxima `≤ 44·W + yl·(128·W)`;
* the fixed part: `modinv_le` (ModInv by rounds), `costG_le` (subMod2N), the rest unfolded exactly.
-/

namespace FvModexp.Amd64.Q.BudE

open Janus Janus.Contracts FvModexp
open FvModexp.Exp (supN supU)
open FvModexp.Amd64.Q.BudW (bs_le opC_eq rnd_le)
open FvModexp.Amd64.ExpEven (NBudO ODem needO cD CQB)

/-! ## the division bound -/

/-- the level-dependent division bound of an inner `nat.expNN` call (EvInst's `cDE x a l`) at levels `l ≤ 6 M + 12` -/
theorem cD_le {x a l M : Nat} (hx : x ≤ M) (ha : a ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) (hl : l ≤ 6 * M + 12) :
    cD (needO x a) l (max (2 * a + 1) x) a ≤ 16 * BudQ.opC M := by
  rw [opC_eq]
  have hA : max (2 * a + 1) x ≤ 2 * M + 1 := by omega
  simp only [cD, CQB, needO, stkRes_eq]
  have r1 := rnd_le (23 * a); have r2 := rnd_le (x + 1); have r3 := rnd_le a; have r4 := rnd_le (2 * a)
  generalize max (2 * a + 1) x = A at hA ⊢
  generalize StackNat.rnd (23 * a) = c1 at r1 ⊢
  generalize StackNat.rnd (x + 1) = c2 at r2 ⊢
  generalize StackNat.rnd a = c3 at r3 ⊢
  generalize StackNat.rnd (2 * a) = c4 at r4 ⊢
  split <;> omega

/-! ## the Montgomery windows at level `l`, any division bound `D` -/

set_option maxHeartbeats 16000000 in
/-- the windows' budget demand at level `l` -/
theorem odem {n xl l D M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) (hl : l ≤ 6 * M + 12) :
    ODem D xl n l ≤ 2 * D + 6 * BudQ.opC M := by
  rw [opC_eq]
  simp only [ODem, ExpEven.xnN4, ExpEven.xnN2, W4Pro.xjBud, W2Pro.xjBud, stackNatCost, allocCost,
    ← Nat.add_max_add_left, ← Nat.add_max_add_right, Nat.max_le]
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r1' := rnd_le (11 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n
  have r4 := rnd_le (2 * n)
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 ⊢
  generalize StackNat.rnd (11 * n) = a' at r1' ⊢
  generalize StackNat.rnd (xl - n + 1) = c1 at r2 ⊢
  generalize StackNat.rnd n = c at r3 ⊢
  generalize StackNat.rnd (2 * n) = d at r4 ⊢
  and_intros <;> omega

set_option maxHeartbeats 16000000 in
/-- window-4's charged cost at level `l` -/
theorem ocost4L {n xl l D M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) (hl : l ≤ 6 * M + 12) :
    W4Pro.W4Cost n xl D l ≤ 2 * D + 6 * BudQ.opC M := by
  rw [opC_eq]
  simp only [W4Pro.W4Cost, W4Pro.xnPreM, W4Pro.xjPre, W4Pro.lvT, W4Pro.lvU, stackNatCost, allocCost,
    ← Nat.add_max_add_left, ← Nat.add_max_add_right, Nat.max_le]
  have mn := BudQ.makeCost_le16 n
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (23 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize makeCost n = K2 at mn ⊢
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (23 * n) = a at r1 ⊢
  generalize StackNat.rnd (xl - n + 1) = c1 at r2 ⊢
  generalize StackNat.rnd n = c at r3 ⊢
  generalize StackNat.rnd (2 * n) = d at r4 ⊢
  and_intros <;> omega

set_option maxHeartbeats 16000000 in
/-- window-2's charged cost at level `l` -/
theorem ocost2L {n xl l D M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) (hl : l ≤ 6 * M + 12) :
    W2Pro.W2Cost n xl D l ≤ 2 * D + 6 * BudQ.opC M := by
  rw [opC_eq]
  simp only [W2Pro.W2Cost, W2Pro.xnPreM, W2Pro.xjPre, W2Pro.lvT, W2Pro.lvU, stackNatCost, allocCost,
    ← Nat.add_max_add_left, ← Nat.add_max_add_right, Nat.max_le]
  have mn := BudQ.makeCost_le16 n
  have b1 := bs_le (8 * n); have b2 := bs_le (8 * (2 * n + 4))
  have mk := BudQ.makeCost_le16 (1 + 128 * n / 64 + 1)
  have r1 := rnd_le (11 * n); have r2 := rnd_le (xl - n + 1); have r3 := rnd_le n; have r4 := rnd_le (2 * n)
  generalize makeCost n = K2 at mn ⊢
  generalize blockSize (8 * n) true = B1 at b1 ⊢
  generalize blockSize (8 * (2 * n + 4)) true = B2 at b2 ⊢
  generalize makeCost (1 + 128 * n / 64 + 1) = K1 at mk ⊢
  generalize StackNat.rnd (11 * n) = a at r1 ⊢
  generalize StackNat.rnd (xl - n + 1) = c1 at r2 ⊢
  generalize StackNat.rnd n = c at r3 ⊢
  generalize StackNat.rnd (2 * n) = d at r4 ⊢
  and_intros <;> omega

theorem ocostL {n xl yl l D M : Nat} (hnM : n ≤ M) (hxM : xl ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) (hl : l ≤ 6 * M + 12) :
    ExpOdd.OCost n xl yl D l ≤ 2 * D + 6 * BudQ.opC M := by
  unfold ExpOdd.OCost
  split
  · exact ocost4L hnM hxM hM hM1 hl
  · exact ocost2L hnM hxM hM hM1 hl


/-! ## `nat.rem`, `nat.expNNSlow` at level `l` (length `a ≤ M`) -/

/-- the bridged `nat.rem` -/
theorem remL {l xl a M : Nat} (hx : xl ≤ M) (ha : a ≤ M) (hM : M ≤ 128) :
    RemInst.remC l xl a ≤ 8 * BudQ.opC M + 160 * l := by
  have hm1 := BudQ.makeCost_le16 xl
  have hm2 := BudQ.makeCost_le16 (xl + 1)
  have hm3 := BudQ.makeCost_le16 (xl - a + 1)
  have hm4 : makeCost 1 = 40 := by decide
  have hd : Q.drsCQ (xl + 1) a ≤ (if a < 40 then 0 else 560 * (xl + 1) + 88 * a + 1400) := by
    split
    · rw [Q.drsCQ_small (by assumption)]; exact Nat.le_refl _
    · exact Q.drsCQ_le (by omega) (by omega)
  rw [opC_eq]
  simp only [RemInst.remC, RemInst.brC, Q.NatDiv.costQ, Q.DivLarge.costQ, Q.NatRem.need, stkRes_eq]
  split at hd <;> omega

/-- the bridged Q-form `nat.expNNSlow` -/
theorem slowL {l xl yl a M : Nat} (hx : xl ≤ M) (ha : a ≤ M) (hM : M ≤ 128) (hM1 : 1 ≤ M) :
    ExpSlow.slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH l xl yl a ≤
      makeCost xl + 8 * BudQ.opC M + yl * (128 * BudQ.opC M) + 160 * l := by
  simp only [ExpSlow.slowBr, ExpSlow.costQ, ExpSlow.needH, stkRes_eq]
  have hxa : max xl a ≤ M := by omega
  have hS := ExpSlow.sq_le (M := max xl a) (by omega)
  have hMu := ExpSlow.mul_le (M := max xl a) (xl := xl) (by omega) (Nat.le_max_left _ _)
  have hD := ExpSlow.div_le (M := max xl a) (n := a) (by omega) (Nat.le_max_right _ _)
  rw [opC_eq]
  generalize supN sqrCQ (max xl a) = s1 at hS ⊢
  generalize supN (fun j => mulCQ j xl) (2 * max xl a) = s2 at hMu ⊢
  generalize supN (fun j => NatDiv.costQ drsCQ j a) (3 * max xl a) = s3 at hD ⊢
  have haA : a ≤ max xl a := Nat.le_max_right _ _
  generalize max xl a = A at hxa hS hMu hD haA ⊢
  have hsum : s1 + s2 + s3 ≤ 2 * (2048 * M + 2072) := by
    by_cases h40 : a < 40
    · rw [if_pos h40] at hD; omega
    · rw [if_neg h40] at hD; omega
  have hm : 64 * yl * (s1 + s2 + s3) ≤ yl * (128 * (2048 * M + 2072)) := by
    rw [Nat.mul_comm 64 yl, Nat.mul_assoc]; exact Nat.mul_le_mul_left yl (by omega)
  omega

/-! ## the inner `nat.expNN` calls (EvenRow's `bUC`/`cUC`, unfolded) -/

/-- EvInst's `cDE` -/
@[reducible] def dE (x a l : Nat) : Nat := cD (needO x a) l (max (2 * a + 1) x) a

/-- the inner calls' budget bound (box maximum; EvenRow's `bUC`) -/
def bU : Nat → Nat → Nat → Nat → Nat → Nat :=
  supU (fun x y a l k => NBudO (dE x a l) RemInst.remC
    (ExpSlow.slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH)
    (P2D.costP P2W2.costB P2W4.costB) x y a l k)

/-- the inner calls' cost bound (box maximum; EvenRow's `cUC`) -/
def cU : Nat → Nat → Nat → Nat → Nat → Nat :=
  supU (fun x y a l k => ExpN.NCost (dE x a l) RemInst.remC
    (ExpSlow.slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH)
    (P2D.costP P2W2.costB P2W4.costB) x y a l k)

set_option maxHeartbeats 4000000 in
/-- one inner `nat.expNN` call (modulus length `a ≤ n`, level `l ≤ 6 n + 12`, `log2 m = k ≤ 64 n`): budget and charged
cost, every branch of the path max -/
theorem inner {xl yl n a l k : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128)
    (ha : a ≤ n) (hl : l ≤ 6 * n + 12) (hk : k ≤ 64 * n) :
    NBudO (dE xl a l) RemInst.remC (ExpSlow.slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH)
        (P2D.costP P2W2.costB P2W4.costB) xl yl a l k ≤
      44 * BudQ.opC (max xl n) + yl * (128 * BudQ.opC (max xl n)) ∧
    ExpN.NCost (dE xl a l) RemInst.remC (ExpSlow.slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH)
        (P2D.costP P2W2.costB P2W4.costB) xl yl a l k ≤
      44 * BudQ.opC (max xl n) + yl * (128 * BudQ.opC (max xl n)) := by
  have hM : max xl n ≤ 128 := by omega
  have hxM := Nat.le_max_left xl n
  have hnM := Nat.le_max_right xl n
  have hl' : l ≤ 6 * max xl n + 12 := by omega
  have hR := remL (l := l) (xl := xl) (a := a) hxM (by omega) hM
  have hS := slowL (l := l) (xl := xl) (yl := yl) (a := a) hxM (by omega) hM (by omega)
  have hP := Q.BudP2.cP_le (ℓ := l) (yl := yl) hx hn0 hn hk
  have hD : dE xl a l ≤ 16 * BudQ.opC (max xl n) := cD_le (x := xl) (a := a) (l := l) hxM (by omega) hM (by omega) hl'
  have hOD := odem (n := a) (xl := xl) (l := l) (D := dE xl a l) (by omega) hxM hM (by omega) hl'
  have hOC := ocostL (n := a) (xl := xl) (yl := yl) (l := l) (D := dE xl a l) (by omega) hxM hM (by omega) hl'
  have m1 : makeCost 1 = 40 := by decide
  have ma := BudQ.makeCost_le16 a; have mx := BudQ.makeCost_le16 xl
  have hW := opC_eq (max xl n)
  simp only [NBudO, ExpEven.NBudE, ExpN.NCost]
  generalize dE xl a l = D at hD hOD hOC ⊢
  generalize ODem D xl a l = od at hOD ⊢
  generalize ExpOdd.OCost a xl yl D l = oc at hOC ⊢
  generalize RemInst.remC l xl a = cr at hR ⊢
  generalize ExpSlow.slowBr (ExpSlow.costQ sqrCQ mulCQ (NatDiv.costQ drsCQ)) ExpSlow.needH l xl yl a = cs at hS ⊢
  generalize P2D.costP P2W2.costB P2W4.costB l xl yl k = cp at hP ⊢
  rw [Nat.mul_left_comm yl 128] at hS ⊢; rw [Nat.mul_left_comm yl 64] at hP
  generalize yl * BudQ.opC (max xl n) = Y at hS hP ⊢
  generalize BudQ.opC (max xl n) = W at hR hS hP hD hOD hOC hW ⊢
  generalize makeCost a = ka at ma ⊢
  generalize makeCost xl = kx at mx hS
  generalize max xl n = M at hR hS hP hD hOD hOC hW hM hxM hnM hl'
  constructor <;> omega

/-- the box maximum is below any bound of the box -/
theorem supU_le (f : Nat → Nat → Nat → Nat → Nat → Nat) (x y a l k B : Nat)
    (h : ∀ a0 l0 k0, a0 ≤ a → l0 ≤ l → k0 ≤ k → f x y a0 l0 k0 ≤ B) : supU f x y a l k ≤ B := by
  unfold supU
  exact ExpSlow.supN_le_const _ _ a fun a0 ha => ExpSlow.supN_le_const _ _ l fun l0 hl =>
    ExpSlow.supN_le_const _ _ k fun k0 hk => h a0 l0 k0 ha hl hk

/-- both inner calls' box maxima (level box `L ≤ 6·n + 12`) -/
theorem innerU {xl yl n L : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) (hL : L ≤ 6 * n + 12) :
    bU xl yl n L (64 * n) ≤ 44 * BudQ.opC (max xl n) + yl * (128 * BudQ.opC (max xl n)) ∧
    cU xl yl n L (64 * n) ≤ 44 * BudQ.opC (max xl n) + yl * (128 * BudQ.opC (max xl n)) :=
  ⟨supU_le _ _ _ _ _ _ _ fun _ _ _ ha hl hk => (inner hx hn0 hn ha (by omega) hk).1,
   supU_le _ _ _ _ _ _ _ fun _ _ _ ha hl hk => (inner hx hn0 hn ha (by omega) hk).2⟩

/-! ## the fixed part: `modularInverseModPowerOfTwo` (Q-form, by rounds), `subMod2N` (arm64 BudEvenQ copies) -/

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

/-- **`heven`**: `nat.expNNEven`'s cost at the top (EvenRow's `cE 0`, unfolded) -/
theorem heven {xl yl n : Nat} (hx : xl ≤ 128) (hn0 : 0 < n) (hn : n ≤ 128) :
    ExpEven.costE bU cU sqrCQ mulCQ 0 xl yl n ≤ 120 * BudQ.opC (max xl n) + yl * (256 * BudQ.opC (max xl n)) := by
  have hL3 : ExpEven.wL3 0 n ≤ 6 * n + 12 := by simp only [ExpEven.wL3, ExpEven.wL2, StackNat.rnd]; omega
  have hL4 : ExpEven.wL4 0 n ≤ 6 * n + 12 := by simp only [ExpEven.wL4, ExpEven.wL3, ExpEven.wL2, StackNat.rnd]; omega
  have hC1 := (innerU (yl := yl) hx hn0 hn hL3).2
  obtain ⟨hB2, hC2⟩ := innerU (yl := yl) hx hn0 hn hL4
  have hM : max xl n ≤ 128 := by omega
  have hnM := Nat.le_max_right xl n
  have hMI := modinv_le (ml := n) (M := max xl n) hn0 hnM hM
  have hG := costG_le hn
  simp only [ExpEven.costE, ExpEven.eC1, ExpEven.eC2]
  generalize bU xl yl n (ExpEven.wL4 0 n) (64 * n) = B2 at hB2 ⊢
  generalize cU xl yl n (ExpEven.wL3 0 n) (64 * n) = C1 at hC1 ⊢
  generalize cU xl yl n (ExpEven.wL4 0 n) (64 * n) = C2 at hC2 ⊢
  generalize ModInv.cost sqrCQ mulCQ n (64 * n) = MI at hMI ⊢
  generalize SubMod2N.costG (64 * n) = G at hG ⊢
  rw [Nat.mul_left_comm yl 128] at hB2 hC1 hC2; rw [Nat.mul_left_comm yl 256]
  generalize yl * BudQ.opC (max xl n) = Y at hB2 hC1 hC2 ⊢
  have hW := opC_eq (max xl n)
  generalize BudQ.opC (max xl n) = W at hB2 hC1 hC2 hW ⊢
  generalize max xl n = M at hB2 hC1 hC2 hW hMI hM hnM ⊢
  simp only [ExpEven.mulE, ExpEven.mulB, stkRes_eq, ModInv.D, ModInv.NW, stackNatCost, makeB, allocCost,
    ExpEven.wL4, ExpEven.wL3, ExpEven.wL2, StackNat.rnd] at hB2 hC1 hC2 ⊢
  omega

end FvModexp.Amd64.Q.BudE
