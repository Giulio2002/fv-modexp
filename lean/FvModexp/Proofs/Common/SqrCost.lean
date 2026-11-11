import FvModexp.Proofs.Common.StackNatMath

/-!
# Budgets and stack windows of the squaring SCC `{nat.sqr, karatsubaSqr}` (ISA independent; agent divmc)

go-bigmodexpfix natmul.go:73 (`nat.sqr`) and :257 (`karatsubaSqr`). Allocation budget (the runtime's `b`):
* `nat.sqr(n)`: `z.make(2n)` (≤ `makeB (2n)`), then for `n ≥ 12` the callee `basicSqr` / `karatsubaSqr` at the same
  stack length `ℓ`: `ksqrC ℓ n` (`basicSqr`: `stk.nat(2n)` = `stackNatCost ℓ (2n)`).
* `karatsubaSqr(n ≥ 80)`: `stk.nat(2·n2 + 1)`, `tx.Sub`, three `nat.sqr` on operands of ≤ `n2` words at stack length
  `ℓ + rnd (2·n2 + 1)`, two `z1.Add` (each `Int.Add`/`Sub` ≤ `asB (2·n2 + 1)`), `addTo` (no allocation).
The bounds are monotone in `ℓ` and `n` (`ksqrC_mono`, `sqrC_mono`), so a call on a shorter operand (`x[:n2].norm()`)
stays within the nominal allowance.
-/

namespace FvModexp

/-- a bound of `nat.make(k)` (`makeCap k ≤ k + 4`) -/
def makeB (k : Nat) : Nat := allocCost (8 * (k + 4))

/-- a bound of one `(*Int).Add` / `(*Int).Sub` on operands of at most `k` words (`nat.add`/`nat.sub` make ≤ `k + 1`) -/
def asB (k : Nat) : Nat := allocCost (8 * (k + 5))

/-- `karatsubaSqr(stk, z, x)` with `len x = n`, at stack length `ℓ` -/
def ksqrC (ℓ n : Nat) : Nat :=
  stackNatCost ℓ (2 * n) +
    if h : 80 ≤ n then
      stackNatCost ℓ (2 * ((n + 1) / 2) + 1) + 3 * asB (2 * ((n + 1) / 2) + 1) +
        3 * (makeB (2 * ((n + 1) / 2)) + ksqrC (ℓ + (2 * ((n + 1) / 2) + 1 + 3) / 4 * 4) ((n + 1) / 2))
    else 0
termination_by n
decreasing_by omega

/-- `z.sqr(stk, x)` with `len x = n`, at stack length `ℓ` -/
def sqrC (ℓ n : Nat) : Nat := makeB (2 * n) + if 12 ≤ n then ksqrC ℓ n else 0

theorem stackNatCost_mono {ℓ ℓ' n n' : Nat} (h1 : ℓ ≤ ℓ') (h2 : n ≤ n') : stackNatCost ℓ n ≤ stackNatCost ℓ' n' := by
  unfold stackNatCost allocCost; omega

theorem asB_mono {k k' : Nat} (h : k ≤ k') : asB k ≤ asB k' := by unfold asB allocCost; omega

theorem makeB_mono {k k' : Nat} (h : k ≤ k') : makeB k ≤ makeB k' := by unfold makeB allocCost; omega

theorem makeCost_le_makeB (k : Nat) : makeCost k ≤ makeB k := by
  unfold makeCost makeB makeCap allocCost; split <;> omega

/-- the large case of `ksqrC`, unfolded once -/
theorem ksqrC_big {ℓ n : Nat} (h : 80 ≤ n) : ksqrC ℓ n = stackNatCost ℓ (2 * n) +
    (stackNatCost ℓ (2 * ((n + 1) / 2) + 1) + 3 * asB (2 * ((n + 1) / 2) + 1) +
      3 * (makeB (2 * ((n + 1) / 2)) + ksqrC (ℓ + (2 * ((n + 1) / 2) + 1 + 3) / 4 * 4) ((n + 1) / 2))) := by
  rw [ksqrC, dif_pos h]

theorem ksqrC_small {ℓ n : Nat} (h : n < 80) : ksqrC ℓ n = stackNatCost ℓ (2 * n) := by
  rw [ksqrC, dif_neg (by omega)]; rfl

theorem ksqrC_mono : ∀ (n' ℓ ℓ' n : Nat), ℓ ≤ ℓ' → n ≤ n' → ksqrC ℓ n ≤ ksqrC ℓ' n' := by
  intro n'
  induction n' using Nat.strongRecOn with
  | _ n' ih =>
    intro ℓ ℓ' n h1 h2
    have hs := stackNatCost_mono (n := 2 * n) (n' := 2 * n') h1 (by omega)
    by_cases hn : 80 ≤ n
    · rw [ksqrC_big (ℓ := ℓ) hn, ksqrC_big (ℓ := ℓ') (n := n') (by omega)]
      have e1 := stackNatCost_mono (n := 2 * ((n + 1) / 2) + 1) (n' := 2 * ((n' + 1) / 2) + 1) h1 (by omega)
      have e2 := asB_mono (k := 2 * ((n + 1) / 2) + 1) (k' := 2 * ((n' + 1) / 2) + 1) (by omega)
      have e3 := makeB_mono (k := 2 * ((n + 1) / 2)) (k' := 2 * ((n' + 1) / 2)) (by omega)
      have e4 := ih ((n' + 1) / 2) (by omega) (ℓ + (2 * ((n + 1) / 2) + 1 + 3) / 4 * 4)
        (ℓ' + (2 * ((n' + 1) / 2) + 1 + 3) / 4 * 4) ((n + 1) / 2) (by omega) (by omega)
      omega
    · rw [ksqrC_small (by omega)]
      by_cases hn' : 80 ≤ n'
      · rw [ksqrC_big (ℓ := ℓ') hn']; omega
      · rw [ksqrC_small (by omega)]; omega

theorem sqrC_mono {ℓ ℓ' n n' : Nat} (h1 : ℓ ≤ ℓ') (h2 : n ≤ n') : sqrC ℓ n ≤ sqrC ℓ' n' := by
  unfold sqrC
  have := makeB_mono (k := 2 * n) (k' := 2 * n') (by omega)
  by_cases hn : 12 ≤ n
  · rw [if_pos hn, if_pos (by omega)]; have := ksqrC_mono n' ℓ ℓ' n h1 h2; omega
  · rw [if_neg hn]; split <;> omega

/-- an inner `nat.sqr` of `karatsubaSqr(n)` on `m ≤ n2` words at the inner stack length -/
theorem sqrC_le_inner {ℓ n m : Nat} (hm : m ≤ (n + 1) / 2) :
    sqrC ℓ m ≤ makeB (2 * ((n + 1) / 2)) + ksqrC ℓ ((n + 1) / 2) := by
  unfold sqrC
  have := makeB_mono (k := 2 * m) (k' := 2 * ((n + 1) / 2)) (by omega)
  split
  · have := ksqrC_mono ((n + 1) / 2) ℓ ℓ m (Nat.le_refl _) hm; omega
  · omega

/-! ## Stack windows (arm64 frames: `nat.sqr` 176 + 64 above, `karatsubaSqr` 320 + 48 above; amd64 equal) -/

/-- the window of `karatsubaSqr` on `n` words: its frame (320) above the deepest non-recursive callee
(`(*Int).Add/Sub`, 4560) plus the nested `nat.sqr` windows (`16` bytes per word) -/
def ksqrW (n : Nat) : Nat := 16 * n + 4880

/-- the window of `nat.sqr` on `n` words: `karatsubaSqr`'s one frame (176) further down -/
def sqrW (n : Nat) : Nat := ksqrW n + 176

/-- an inner `nat.sqr` (≤ `n2` words) at `karatsubaSqr`'s `SP - 320` fits in `karatsubaSqr`'s window -/
theorem sqrW_inner {n m : Nat} (hn : 80 ≤ n) (hm : m ≤ (n + 1) / 2) : sqrW m + 320 ≤ ksqrW n := by
  unfold sqrW ksqrW; omega

end FvModexp
