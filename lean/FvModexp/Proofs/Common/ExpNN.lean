import FvModexp.Proofs.Common.ExpOdd
import FvModexp.Proofs.Common.ExpSlow
import FvModexp.Proofs.Common.ExpEven
import EthLib.Execution.Evm.PowMod
/-
  ExpNN: the top of the Nat-level exponentiation layer.
    nat.expNN            nat.go:639-730   (dispatch: m = 1, y = 0, x = 0, x = 1, y = 1, slow/small-y, odd, 2^k, even)
    (*Int).exp           int.go:575-608   (as reached from (*Int).Exp, int.go:567)
    (*Int).Mod           int.go:325-339   (+ (*Int).QuoRem int.go:299-303)
    geth bigModExp.Run   core/vm/contracts.go:684-693 (the `switch` on mod / base, Nat level)
  and their correctness  `= b ^ e % m`, plus the bridge to EthLib's `EthLib.Execution.Evm.powMod`.
  Source: github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/{nat,int}.go,
  github.com/ethereum/go-ethereum@v1.17.10/core/vm/contracts.go.
-/
namespace FvModexp.Exp

/-! ### EthLib `powMod` -/

/-- EthLib's square-and-multiply `powMod` is `b ^ e % m` (for every `m`, including `0`). -/
theorem powMod_eq (b e m : Nat) : EthLib.Execution.Evm.powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn generalizing b with
  | _ e ih =>
    rw [EthLib.Execution.Evm.powMod.eq_def]
    split
    · rename_i h; subst h; simp
    · rename_i h
      simp only
      rw [ih (e / 2) (by omega)]
      have hsq : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, Nat.pow_mul, Nat.pow_two]
      rw [hsq]
      split
      · rename_i ho
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_succ]
        congr 2; omega
      · rename_i he
        congr 2; omega

/-! ### `nat.expNN` (nat.go:639) -/

/-- `nlz(w)` for a word `w < 2^64` (arith.go:58, `bits.LeadingZeros`). -/
def nlzW (w : Nat) : Nat := 64 - bitLen w

/-- `nat.expNN(x, y, m, slow)` (nat.go:639-730). `f` is a recursion budget: Go's `expNN` re-enters itself only
through `expNNEven`, whose two recursive calls have moduli `2^n` and odd `m2`, which never reach `expNNEven`
again; `expNN 2` is therefore the Go function (proved below: every branch is exact for `f ≥ 2`). -/
def expNN : Nat → Nat → Nat → Nat → Bool → Nat
  | 0, _, _, _, _ => 0
  | f + 1, x, y, m, slow =>
    if m = 1 then 0                                          -- len(m) == 1 && m[0] == 1: z.setWord(0)
    else if y = 0 then 1                                     -- len(y) == 0: z.setWord(1)
    else if x = 0 then 0                                     -- len(x) == 0: z.setWord(0)
    else if x = 1 then 1                                     -- len(x) == 1 && x[0] == 1: z.setWord(1)
    else if y = 1 ∧ m = 0 then x                             -- len(y) == 1 && y[0] == 1 && len(m) == 0: z.set(x)
    else if y = 1 then x % m                                 -- len(y) == 1 && y[0] == 1: z.rem(stk, x, m)
    else if m ≠ 0 then                                       -- len(m) != 0
      if slow then expNNSlow x y m
      else if nlen y = 1 ∧ 64 - 5 ≤ nlzW (wd y 0) then expNNSlow x y m   -- nlz(y[0]) >= _W - 5
      else if m % 2 = 1 then expNNOdd x y m                  -- m[0]&1 == 1
      else match isPow2 m with                               -- if logM, ok := m.isPow2(); ok
        | some logM => expNNPowerOfTwo 2 x y logM
        | none => expNNEven (fun x y m => expNN f x y m false) x y m
    else expNNSlow x y m                                     -- m == 0

theorem tz_two_pow (k : Nat) : tz (2 ^ k) = k := by
  induction k with
  | zero => unfold tz; simp
  | succ k ih =>
    unfold tz
    rw [dif_neg (Nat.ne_of_gt (Nat.two_pow_pos _))]
    have h2 : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ]; simp
    rw [if_neg (by omega), Nat.pow_succ, Nat.mul_div_cancel _ (by omega), ih]; omega

theorem isPow2_two_pow (k : Nat) : isPow2 (2 ^ k) = some k := by
  unfold isPow2; rw [tz_two_pow]; simp

theorem isPow2_some {m L : Nat} (h : isPow2 m = some L) : m = 2 ^ L := by
  unfold isPow2 at h
  split at h
  · rename_i he; cases h; exact he
  · cases h

theorem lt_B_of_pow {L : Nat} (h : 2 ^ L < 2 ^ B) : L < B :=
  (Nat.pow_lt_pow_iff_right (by omega)).mp h

/-- The non-recursive branches, for any budget `f ≥ 1`, when `m` is odd or a power of two. -/
theorem expNN_correct_base (f x y m : Nat) (slow : Bool) (hf : 1 ≤ f) (hm : 0 < m) (hmB : m < 2 ^ B)
    (hshape : m % 2 = 1 ∨ ∃ k, m = 2 ^ k) : expNN f x y m slow = x ^ y % m := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  unfold expNN
  by_cases h1 : m = 1
  · rw [if_pos h1, h1, Nat.mod_one]
  rw [if_neg h1]
  have hm2 : 1 < m := by omega
  by_cases hy0 : y = 0
  · rw [if_pos hy0, hy0, Nat.pow_zero, Nat.mod_eq_of_lt hm2]
  rw [if_neg hy0]
  by_cases hx0 : x = 0
  · rw [if_pos hx0, hx0, Nat.zero_pow (by omega), Nat.zero_mod]
  rw [if_neg hx0]
  by_cases hx1 : x = 1
  · rw [if_pos hx1, hx1, Nat.one_pow, Nat.mod_eq_of_lt hm2]
  rw [if_neg hx1, if_neg (by omega)]
  by_cases hy1 : y = 1
  · rw [if_pos hy1, hy1, Nat.pow_one]
  rw [if_neg hy1, if_pos (by omega)]
  have hy2 : 2 ≤ y := by omega
  have hslow := expNNSlow_correct x y m hy2
  rw [if_neg (by omega)] at hslow
  split
  · exact hslow
  split
  · exact hslow
  split
  · exact expNNOdd_correct x y m (by assumption) (by omega)
  rename_i hne
  rcases hshape with ho | ⟨k, rfl⟩
  · exact absurd ho hne
  rw [isPow2_two_pow]
  simp only
  have hk : 1 ≤ k := by
    refine Nat.one_le_iff_ne_zero.mpr (fun h0 => ?_); rw [h0] at h1; exact h1 rfl
  exact expNNPowerOfTwo_correct 2 x y k (by omega) (by omega) (by omega) hk (lt_B_of_pow hmB)

/-- **expNN is modular exponentiation**: for `m > 0` (and `m < 2^(2^64)`, any Go `nat`), budget `f ≥ 2`. -/
theorem expNN_correct (f x y m : Nat) (slow : Bool) (hf : 2 ≤ f) (hm : 0 < m) (hmB : m < 2 ^ B) :
    expNN f x y m slow = x ^ y % m := by
  by_cases hshape : m % 2 = 1 ∨ ∃ k, m = 2 ^ k
  · exact expNN_correct_base f x y m slow (by omega) hm hmB hshape
  have hme : m % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exact h
    · exact absurd (Or.inl h) hshape
  have hnp : isPow2 m = none := by
    cases hp : isPow2 m with
    | none => rfl
    | some L => exact absurd (Or.inr ⟨L, isPow2_some hp⟩) hshape
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  unfold expNN
  have h1 : m ≠ 1 := by omega
  rw [if_neg h1]
  have hm2 : 1 < m := by omega
  by_cases hy0 : y = 0
  · rw [if_pos hy0, hy0, Nat.pow_zero, Nat.mod_eq_of_lt hm2]
  rw [if_neg hy0]
  by_cases hx0 : x = 0
  · rw [if_pos hx0, hx0, Nat.zero_pow (by omega), Nat.zero_mod]
  rw [if_neg hx0]
  by_cases hx1 : x = 1
  · rw [if_pos hx1, hx1, Nat.one_pow, Nat.mod_eq_of_lt hm2]
  rw [if_neg hx1, if_neg (by omega)]
  by_cases hy1 : y = 1
  · rw [if_pos hy1, hy1, Nat.pow_one]
  rw [if_neg hy1, if_pos (by omega)]
  have hy2 : 2 ≤ y := by omega
  have hslow := expNNSlow_correct x y m hy2
  rw [if_neg (by omega)] at hslow
  split
  · exact hslow
  split
  · exact hslow
  rw [if_neg (by omega), hnp]
  simp only
  refine expNNEven_correct _ x y m hm hme ?_
  intro m' hm' hdvd hsh
  exact expNN_correct_base f' x y m' false (by omega) hm'
    (Nat.lt_of_le_of_lt (Nat.le_of_dvd hm hdvd) hmB) hsh

/-! ### `(*Int).exp`, `(*Int).Mod` (int.go) -/

/-- A Go `big.Int` value: `{neg bool; abs nat}` (int.go:33). -/
structure GoInt where
  neg : Bool
  abs : Nat
deriving DecidableEq

/-- `(*Int).exp(x, y, m, slow)` (int.go:575-608) for non-nil `m`; `modInverse` is `(*Int).ModInverse`
(int.go:890), `none` meaning its `nil` result. -/
def intExp (modInverse : GoInt → GoInt → Option GoInt) (x y m : GoInt) (slow : Bool) : Option GoInt :=
  if y.neg ∧ m.abs = 0 then some ⟨false, 1⟩                 -- if y.neg { if m == nil || len(m.abs) == 0 { SetInt64(1) } }
  else
    let xWords : Option Nat :=                              -- xWords := x.abs
      if y.neg then (modInverse x m).map GoInt.abs else some x.abs   -- inverse := new(Int).ModInverse(x, m)
    match xWords with
    | none => none                                          -- if inverse == nil { return nil }
    | some xw =>
      let z := expNN 2 xw y.abs m.abs slow                  -- z.abs = z.abs.expNN(nil, xWords, yWords, mWords, slow)
      let neg := decide (z ≠ 0) && x.neg && decide (y.abs % 2 = 1)   -- len(z.abs) > 0 && x.neg && len(yWords) > 0 && yWords[0]&1 == 1
      if neg ∧ m.abs ≠ 0 then some ⟨false, m.abs - z⟩       -- z.abs = z.abs.sub(mWords, z.abs); z.neg = false
      else some ⟨neg, z⟩

/-- `(*Int).Exp(x, y, m)` (int.go:567). -/
def intExpPub (modInverse : GoInt → GoInt → Option GoInt) (x y m : GoInt) : Option GoInt :=
  intExp modInverse x y m false

/-- `(*Int).Mod(x, y)` (int.go:325-339) via `QuoRem` (int.go:299-303: `r.abs = x.abs mod y.abs`,
`r.neg = len(r.abs) > 0 && x.neg`); a negative remainder is shifted by `|y|` (`z.Add(z, y0)` / `z.Sub(z, y0)`,
both giving `|y| - r`). -/
def intMod (x y : GoInt) : GoInt :=
  let r := x.abs % y.abs
  let rneg := decide (r ≠ 0) && x.neg
  if rneg then ⟨false, y.abs - r⟩ else ⟨false, r⟩

/-- **Reachability (path condition).** With a non-negative exponent (`y.neg = false`, as produced by `SetBytes`)
`(*Int).exp` never consults `ModInverse` (hence neither `GCD`, `lehmerGCD`, `lehmerSimulate`, `lehmerUpdate`,
`euclidUpdate`): the result is the same for every `modInverse` behaviour. -/
theorem intExp_modInverse_irrelevant (mi mi' : GoInt → GoInt → Option GoInt) (x y m : GoInt) (slow : Bool)
    (hy : y.neg = false) : intExp mi x y m slow = intExp mi' x y m slow := by
  unfold intExp; simp [hy]

/-- **(*Int).Exp as geth calls it** (`base.Exp(base, exp, mod)`, contracts.go:692): non-negative operands,
`mod > 0` ⇒ the result is the non-negative `Int` with `abs = b ^ e % m`. -/
theorem intExp_correct (mi : GoInt → GoInt → Option GoInt) (b e m : Nat) (hm : 0 < m) (hmB : m < 2 ^ B) :
    intExpPub mi ⟨false, b⟩ ⟨false, e⟩ ⟨false, m⟩ = some ⟨false, b ^ e % m⟩ := by
  unfold intExpPub intExp
  simp only [Bool.false_eq_true, false_and, if_false, Bool.and_false]
  rw [expNN_correct 2 b e m false (by omega) hm hmB]
  simp

/-- `base.Mod(base, mod)` for non-negative operands. -/
theorem intMod_nonneg (b m : Nat) : intMod ⟨false, b⟩ ⟨false, m⟩ = ⟨false, b % m⟩ := by
  unfold intMod; simp

/-- geth's `base.BitLen() == 1` branch (contracts.go:688-690): `base.Mod(base, mod)` is `b ^ e % m`. -/
theorem bitLen_one_mod (b e m : Nat) (hb : bitLen b = 1) :
    (intMod ⟨false, b⟩ ⟨false, m⟩).abs = b ^ e % m := by
  have : b = 1 := by
    unfold bitLen at hb
    split at hb
    · omega
    · rename_i h
      have h2 := Nat.log2_lt h (k := 1)
      simp at h2
      omega
  subst this
  rw [intMod_nonneg]; simp

/-! ### geth `bigModExp.Run`, Nat level (contracts.go:684-693) -/

/-- The value computed by the `switch` of `bigModExp.Run` (contracts.go:684-693) on `base, exp, mod` read by
`SetBytes` (all non-negative): `mod.BitLen() == 0` → zero bytes (value 0); `base.BitLen() == 1` → `base.Mod`;
otherwise `base.Exp(base, exp, mod)`. `ModInverse` is irrelevant (see `intExp_modInverse_irrelevant`); the
`Option.getD` default is never used for `m > 0` (`intExp_correct`). -/
def runValue (b e m : Nat) : Nat :=
  if bitLen m = 0 then 0
  else if bitLen b = 1 then (intMod ⟨false, b⟩ ⟨false, m⟩).abs
  else ((intExpPub (fun _ _ => none) ⟨false, b⟩ ⟨false, e⟩ ⟨false, m⟩).getD ⟨false, 0⟩).abs

theorem bitLen_zero_iff (m : Nat) : bitLen m = 0 ↔ m = 0 := by
  unfold bitLen; split <;> omega

/-- **Run's arithmetic agrees with EthLib**: `runValue b e m` equals `compute`'s
`if modulus = 0 then 0 else powMod base exponent modulus` (EthLib.Execution.Evm.Precompiles.Modexp.Core). -/
theorem runValue_eq_spec (b e m : Nat) (hmB : m < 2 ^ B) :
    runValue b e m = if m = 0 then 0 else EthLib.Execution.Evm.powMod b e m := by
  unfold runValue
  by_cases hm : m = 0
  · rw [if_pos ((bitLen_zero_iff m).mpr hm), if_pos hm]
  rw [if_neg (by rw [bitLen_zero_iff]; exact hm), if_neg hm, powMod_eq]
  split
  · rename_i hb; exact bitLen_one_mod b e m hb
  · rw [intExp_correct _ b e m (by omega) hmB]; rfl

/-- Any Go `nat` built from at most `2^57` bytes (geth: ≤ 1024 bytes) is below `2^(2^64)`. -/
theorem lt_two_pow_B_of_bytes (m k : Nat) (hk : k ≤ 2 ^ 57) (h : m < 256 ^ k) : m < 2 ^ B := by
  refine Nat.lt_of_lt_of_le h ?_
  have : (256 : Nat) ^ k = 2 ^ (8 * k) := by rw [Nat.pow_mul]
  rw [this]
  apply Nat.pow_le_pow_right (by omega)
  rw [B_eq]; omega

end FvModexp.Exp
