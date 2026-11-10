import FvModexp.Proofs.Common.BytesNat
/-!
# bitLen, low64 / Uint64 / IsUint64, Int.SetBytes, and the `(*stack).nat` size rounding

* `natBitLen`   nat.go:342-360 (go-bigmodexpfix) = go1.26.10 math/big nat.go:332-350; `bits.Len` is modelled by `bitsLen`
                (= `Nat.log2 x + 1`, 0 for 0: the mathematical definition of `bits.Len64`, go1.26.10 math/bits/bits.go)
* `low64`       int.go:416-425 (`_W == 64`: the `_W == 32` branch is dead);  `Int.Uint64` int.go:439;  `Int.IsUint64` int.go:453
* `intSetBytes` int.go:518-522 (both copies)
* `stackRound`  nat.go:320 `nr := (n + 3) &^ 3` in `(*stack).nat` (nat.go:319-329)
-/
namespace FvModexp.Mdl

/-- `bits.Len64(x)`: the minimum number of bits to represent `x`. -/
def bitsLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- The smearing `top |= top >> 1; top |= top >> 2; … ; top |= top >> 16 >> 16` (nat.go:350-356). -/
def smear (t : Nat) : Nat :=
  let t := t ||| (t >>> 1)
  let t := t ||| (t >>> 2)
  let t := t ||| (t >>> 4)
  let t := t ||| (t >>> 8)
  let t := t ||| (t >>> 16)
  t ||| (t >>> 16 >>> 16)

/-- nat.go:342 `(x nat) bitLen() int`: `i*_W + bits.Len(top)` with `i = len(x)-1`, `top` the smeared top limb. -/
def natBitLen (x : List Nat) : Nat :=
  if x.length = 0 then 0 else (x.length - 1) * 64 + bitsLen (smear (topLimb x))

/-- int.go:416 `low64(x nat) uint64`. -/
def low64 (x : List Nat) : Nat := match x with | [] => 0 | d :: _ => d

/-- int.go:453 `(*Int).IsUint64`: `!x.neg && len(x.abs) <= 64/_W`. -/
def isUint64 (neg : Bool) (abs : List Nat) : Bool := !neg && decide (abs.length ≤ 1)

/-- int.go:518 `(*Int).SetBytes`: `z.abs = z.abs.setBytes(buf); z.neg = false` (returns `(neg, abs)`). -/
def intSetBytes (buf : List Nat) : Bool × List Nat := (false, natSetBytes buf)

/-! ### smearing preserves the position of the top bit -/

theorem or_shr_log2 (t k : Nat) (h0 : t ≠ 0) : Nat.log2 (t ||| (t >>> k)) = Nat.log2 t := by
  have hle : t ≤ t ||| (t >>> k) := Nat.left_le_or
  have hne : t ||| (t >>> k) ≠ 0 := by omega
  rw [Nat.log2_eq_iff hne]
  refine ⟨Nat.le_trans (Nat.log2_self_le h0) hle, ?_⟩
  exact Nat.or_lt_two_pow Nat.lt_log2_self (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) Nat.lt_log2_self)

theorem or_shr_ne (t k : Nat) (h0 : t ≠ 0) : t ||| (t >>> k) ≠ 0 := by
  have : t ≤ t ||| (t >>> k) := Nat.left_le_or
  omega

theorem smear_log2 (t : Nat) (h0 : t ≠ 0) : smear t ≠ 0 ∧ Nat.log2 (smear t) = Nat.log2 t := by
  unfold smear
  simp only []
  have a1 := or_shr_ne t 1 h0
  have b1 := or_shr_log2 t 1 h0
  generalize t ||| t >>> 1 = t1 at *
  have a2 := or_shr_ne t1 2 a1
  have b2 := or_shr_log2 t1 2 a1
  generalize t1 ||| t1 >>> 2 = t2 at *
  have a3 := or_shr_ne t2 4 a2
  have b3 := or_shr_log2 t2 4 a2
  generalize t2 ||| t2 >>> 4 = t3 at *
  have a4 := or_shr_ne t3 8 a3
  have b4 := or_shr_log2 t3 8 a3
  generalize t3 ||| t3 >>> 8 = t4 at *
  have a5 := or_shr_ne t4 16 a4
  have b5 := or_shr_log2 t4 16 a4
  generalize t4 ||| t4 >>> 16 = t5 at *
  have e : t5 >>> 16 >>> 16 = t5 >>> 32 := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  rw [e]
  exact ⟨or_shr_ne t5 32 a5, by rw [or_shr_log2 t5 32 a5]; omega⟩

theorem smear_zero : smear 0 = 0 := by decide

theorem bitsLen_smear (t : Nat) : bitsLen (smear t) = bitsLen t := by
  by_cases h : t = 0
  · subst h; rw [smear_zero]
  · obtain ⟨h1, h2⟩ := smear_log2 t h
    simp [bitsLen, h, h1, h2]

theorem bitsLen_spec (x : Nat) : x < 2 ^ bitsLen x ∧ (x ≠ 0 → 2 ^ (bitsLen x - 1) ≤ x) := by
  unfold bitsLen
  by_cases h : x = 0
  · subst h; simp
  · simp only [h, if_false, Nat.add_sub_cancel]
    exact ⟨Nat.lt_log2_self, fun _ => Nat.log2_self_le h⟩

theorem topLimb_cons_split (x : List Nat) (hne : x ≠ []) :
    x = x.take (x.length - 1) ++ [topLimb x] := by
  unfold topLimb
  have hl : x.length - 1 < x.length := by cases x <;> simp_all
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  conv => lhs; rw [← List.take_append_drop (x.length - 1) x]
  congr 1
  rw [List.drop_eq_getElem_cons hl]
  have : List.drop (x.length - 1 + 1) x = [] := List.drop_eq_nil_of_le (by omega)
  rw [this]

/-- `bitLen` of a normalised nat is the bit length of its value. -/
theorem natBitLen_spec (x : List Nat) (hw : Wd x) (hn : Normed x) : natBitLen x = bitsLen (val x) := by
  unfold natBitLen
  by_cases h0 : x.length = 0
  · rw [if_pos h0, List.length_eq_zero_iff.1 h0]; rfl
  rw [if_neg h0, bitsLen_smear]
  have hne : x ≠ [] := fun h => h0 (by simp [h])
  have hs := topLimb_cons_split x hne
  have hv : val x = val (x.take (x.length - 1)) + 2 ^ (64 * (x.length - 1)) * topLimb x := by
    conv => lhs; rw [hs]
    rw [val_append]; simp [List.length_take]
  have hlo : val (x.take (x.length - 1)) < 2 ^ (64 * (x.length - 1)) := by
    have := val_lt (hw.take (x.length - 1)); simpa [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)] using this
  have htop : topLimb x ≠ 0 := by
    intro ht
    have := Normed.val_ge hn hne hw
    have : val x < 2 ^ (64 * (x.length - 1)) := by rw [hv, ht]; simpa using hlo
    omega
  have htB : topLimb x < 2 ^ 64 := by
    have : topLimb x ∈ x.take (x.length - 1) ++ [topLimb x] := by simp
    rw [← hs] at this
    exact hw _ this
  have hvne : val x ≠ 0 := by
    have : 2 ^ (64 * (x.length - 1)) * 1 ≤ 2 ^ (64 * (x.length - 1)) * topLimb x := Nat.mul_le_mul_left _ (by omega)
    have := Nat.two_pow_pos (64 * (x.length - 1)); omega
  unfold bitsLen
  rw [if_neg htop, if_neg hvne]
  have hk : Nat.log2 (val x) = 64 * (x.length - 1) + Nat.log2 (topLimb x) := by
    rw [Nat.log2_eq_iff hvne]
    have l1 := Nat.log2_self_le htop
    have l2 : topLimb x < 2 ^ (Nat.log2 (topLimb x) + 1) := Nat.lt_log2_self
    constructor
    · rw [Nat.pow_add, hv]
      have := Nat.mul_le_mul_left (2 ^ (64 * (x.length - 1))) l1
      omega
    · rw [show 64 * (x.length - 1) + Nat.log2 (topLimb x) + 1 = 64 * (x.length - 1) + (Nat.log2 (topLimb x) + 1) by omega,
        Nat.pow_add, hv]
      have := Nat.mul_le_mul_left (2 ^ (64 * (x.length - 1))) (show topLimb x + 1 ≤ 2 ^ (Nat.log2 (topLimb x) + 1) by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  rw [hk]; omega

/-- `low64` of a normalised one-limb-or-less nat is its value; in general it is the value mod 2^64. -/
theorem low64_spec (x : List Nat) (hw : Wd x) : low64 x = val x % 2 ^ 64 := by
  cases x with
  | nil => rfl
  | cons d ds =>
    simp only [low64, val_cons]
    have := (Wd_cons.1 hw).1
    omega

theorem low64_eq_val (x : List Nat) (hw : Wd x) (hl : x.length ≤ 1) : low64 x = val x := by
  match x, hl with
  | [], _ => rfl
  | [d], _ => simp [low64]

/-- For a normalised nat, `len(x) ≤ 1` iff the value fits in 64 bits (so `IsUint64` decides `val < 2^64` for `neg = false`). -/
theorem length_le_one_iff (x : List Nat) (hw : Wd x) (hn : Normed x) : x.length ≤ 1 ↔ val x < 2 ^ 64 := by
  constructor
  · intro hl
    have := val_lt hw
    have : 2 ^ (64 * x.length) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · intro hv
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have hne : x ≠ [] := by intro h; subst h; simp at hlt
    have := Normed.val_ge hn hne hw
    have : 2 ^ 64 ≤ 2 ^ (64 * (x.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem intSetBytes_spec (buf : List Nat) (hb : Bt buf) :
    (intSetBytes buf).1 = false ∧ Wd (intSetBytes buf).2 ∧ Normed (intSetBytes buf).2 ∧
    val (intSetBytes buf).2 = beVal buf ∧ (intSetBytes buf).2.length ≤ (buf.length + 7) / 8 := by
  obtain ⟨a, b, c, d⟩ := natSetBytes_spec buf hb
  exact ⟨rfl, a, b, c, d⟩

/-! ### `(*stack).nat` rounding -/

/-- nat.go:320 `nr := (n + 3) &^ 3` on a 64-bit `int` (no overflow: `n` is a slice length). -/
def stackRound (n : Nat) : Nat := (n + 3) &&& (2 ^ 64 - 1 - 3)

theorem stackRound_eq (n : Nat) (h : n + 3 < 2 ^ 64) : stackRound n = (n + 3) / 4 * 4 := by
  unfold stackRound
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have e1 : (n + 3) / 4 * 4 = ((n + 3) >>> 2) <<< 2 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have e2 : (2 ^ 64 - 1 - 3 : Nat) = (2 ^ 62 - 1) <<< 2 := by decide
  rw [e1, e2, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : 2 ≤ i
  · by_cases hj : i < 64
    · simp [hi, show i - 2 < 62 by omega, show 2 + (i - 2) = i by omega]
    · have : (n + 3).testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, show ¬ (i - 2 < 62) by omega, show 2 + (i - 2) = i by omega, this]
  · simp [hi]

theorem stackRound_bounds (n : Nat) (h : n + 3 < 2 ^ 64) :
    n ≤ stackRound n ∧ stackRound n < n + 4 ∧ stackRound n % 4 = 0 := by
  rw [stackRound_eq n h]; omega

end FvModexp.Mdl
