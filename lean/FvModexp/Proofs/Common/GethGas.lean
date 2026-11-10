import FvModexp.Proofs.Common.Util
import FvModexp.Spec

/-!
# geth's MODEXP gas functions as `Nat` functions, and their agreement with EthLib

Faithful transcriptions of go-ethereum v1.17.10 `core/vm/contracts.go` (GOMODCACHE
`github.com/ethereum/go-ethereum@v1.17.10/core/vm/contracts.go`), with `uint64` overflow checks (`bits.Mul64`/`bits.Add64`
carries) as comparisons with `2^64` and `math.MaxUint64` as `2^64 - 1`. `uint256.Int.BitLen` is `Aux.bitLen`.
`osaka_gas_eq` proves them equal to EthLib's `gasCost` for every fork from Fusaka on, when the lengths pass EIP-7823 (≤ 1024).
-/

namespace FvModexp.Geth

open EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp

/-- `math.MaxUint64`. -/
abbrev maxU64 : Nat := 2 ^ 64 - 1

/-- `modexpIterationCount(expLen, expHead, multiplier)`, contracts.go:509-529. -/
def iterationCount (expLen expHead mult : Nat) : Nat :=
  -- contracts.go:513-519: `if expLen > 32 { carry, count := bits.Mul64(expLen-32, multiplier); if carry > 0 { return MaxUint64 }; ... }`
  if 32 < expLen ∧ 2 ^ 64 ≤ (expLen - 32) * mult then maxU64
  else
    let ic := if 32 < expLen then (expLen - 32) * mult else 0
    let bl := Aux.bitLen expHead
    -- contracts.go:521-527: `if bitLen > 0 { count, carry := bits.Add64(iterationCount, uint64(bitLen-1), 0); if carry > 0 { return MaxUint64 } ... }`
    if 0 < bl ∧ 2 ^ 64 ≤ ic + (bl - 1) then maxU64
    else
      -- contracts.go:529: `return max(iterationCount, 1)`
      max (if 0 < bl then ic + (bl - 1) else ic) 1

/-- `berlinMultComplexity(x)`, contracts.go:470-484. -/
def berlinMultComplexity (x : Nat) : Nat :=
  if 2 ^ 64 ≤ x + 7 then maxU64
  else
    let w := (x + 7) / 8
    if 2 ^ 64 ≤ w * w then maxU64 else w * w

/-- `osakaMultComplexity(x)`, contracts.go:490-503. -/
def osakaMultComplexity (x : Nat) : Nat :=
  if x ≤ 32 then 16
  else
    let r := berlinMultComplexity x
    if 2 ^ 64 ≤ r * 2 then maxU64 else r * 2

/-- `osakaModexpGas(baseLen, expLen, modLen, expHead)`, contracts.go:580-598. -/
def osakaModexpGas (baseLen expLen modLen expHead : Nat) : Nat :=
  let mc := osakaMultComplexity (max baseLen modLen)
  if mc = maxU64 then maxU64
  else
    let ic := iterationCount expLen expHead 16
    if 2 ^ 64 ≤ ic * mc then maxU64 else max (ic * mc) 500

theorem log2_eq_bitLen (h : Nat) : Nat.log2 h = Aux.bitLen h - 1 := by
  unfold Aux.bitLen
  by_cases h0 : h = 0
  · subst h0; first | rfl | simp [Nat.log2_zero]
  · simp [h0]

theorem bitLen_le (h k : Nat) (hk : h < 2 ^ k) : Aux.bitLen h ≤ k := by
  unfold Aux.bitLen
  by_cases h0 : h = 0
  · simp [h0]
  · simp only [h0, if_false]
    have := (Nat.log2_lt h0).2 hk
    omega

theorem iterationCount_eq (fork : Fork) (hf : Spec.PostFusaka fork) (e h : Nat) (he : e ≤ 1024) (hh : h < 2 ^ 256) :
    iterationCount e h 16 = iterations fork e h := by
  have hf' : fork ≥ Fork.fusaka := hf
  have hbl := bitLen_le h 256 hh
  unfold iterationCount iterations
  simp only [hf', if_true, log2_eq_bitLen]
  try rw [show ITERATIONS_PER_EXTRA_EXPONENT_BYTE = 16 from rfl]
  try rw [show EXPONENT_HEAD_BYTES = 32 from rfl]
  generalize Aux.bitLen h = bl at *
  repeat' split
  all_goals omega

theorem iterations_le (fork : Fork) (e h : Nat) (he : e ≤ 1024) (hh : h < 2 ^ 256) : iterations fork e h ≤ 16 * 992 + 255 := by
  have hbl := bitLen_le h 256 hh
  unfold iterations
  simp only [log2_eq_bitLen]
  try rw [show ITERATIONS_PER_EXTRA_EXPONENT_BYTE = 16 from rfl]
  try rw [show EXPONENT_HEAD_BYTES = 32 from rfl]
  generalize Aux.bitLen h = bl at *
  repeat' split
  all_goals omega

theorem osakaMultComplexity_eq (fork : Fork) (hf : Spec.PostFusaka fork) (b m : Nat) (hb : b ≤ 1024) (hm : m ≤ 1024) :
    osakaMultComplexity (max b m) = complexity fork b m := by
  have hf' : fork ≥ Fork.fusaka := hf
  unfold osakaMultComplexity berlinMultComplexity complexity
  simp only [hf', if_true]
  try rw [show SMALL_LENGTH_BYTES = 32 from rfl]
  try rw [show MIN_COMPLEXITY = 16 from rfl]
  try rw [show WORD_BYTES = 8 from rfl]
  have hx : max b m ≤ 1024 := by omega
  generalize max b m = x at *
  have hw : (x + 8 - 1) / 8 ≤ 128 := by omega
  have hw2 : (x + 8 - 1) / 8 * ((x + 8 - 1) / 8) ≤ 128 * 128 := Nat.mul_le_mul hw hw
  rw [show x + 7 = x + 8 - 1 by omega, Nat.pow_two]
  by_cases h32 : x > 32
  · rw [if_pos h32, if_neg (show ¬ x ≤ 32 by omega)]
    repeat' split
    all_goals omega
  · rw [if_neg h32, if_pos (show x ≤ 32 by omega)]

theorem complexity_le (fork : Fork) (hf : Spec.PostFusaka fork) (b m : Nat) (hb : b ≤ 1024) (hm : m ≤ 1024) :
    complexity fork b m ≤ 2 * 128 * 128 := by
  have hf' : fork ≥ Fork.fusaka := hf
  unfold complexity
  simp only [hf', if_true]
  try rw [show SMALL_LENGTH_BYTES = 32 from rfl]
  try rw [show MIN_COMPLEXITY = 16 from rfl]
  try rw [show WORD_BYTES = 8 from rfl]
  have hx : max b m ≤ 1024 := by omega
  generalize max b m = x at *
  have hw : (x + 8 - 1) / 8 ≤ 128 := by omega
  have hw2 : ((x + 8 - 1) / 8) ^ 2 ≤ 128 * 128 := by rw [Nat.pow_two]; exact Nat.mul_le_mul hw hw
  by_cases h32 : x > 32
  · rw [if_pos h32]; omega
  · rw [if_neg h32]; omega

theorem bitLen_zero_iff (h : Nat) : Aux.bitLen h = 0 ↔ h = 0 := by
  unfold Aux.bitLen; by_cases h0 : h = 0 <;> simp [h0]

/-- The bit length of a 4-limb value, by its highest non-zero limb (`uint256.Int.BitLen`, uint256.go:830-841). -/
theorem bitLen_limbs (l0 l1 l2 l3 : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64) :
    Aux.bitLen (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) =
      if l3 ≠ 0 then 192 + Aux.bitLen l3 else if l2 ≠ 0 then 128 + Aux.bitLen l2 else if l1 ≠ 0 then 64 + Aux.bitLen l1
      else Aux.bitLen l0 := by
  have := Util.bl_4 l0 l1 l2 l3 h0 h1 h2
  simp only [Nat.reducePow] at this ⊢
  exact this

/-- For lengths passing EIP-7823 and a 256-bit exponent head, geth's Osaka gas is EthLib's `gasCost` at every fork from Fusaka on
(in particular it is below `2^64`: no `MaxUint64` saturation). -/
theorem osaka_gas_eq (fork : Fork) (hf : Spec.PostFusaka fork) (b e m h : Nat) (hb : b ≤ 1024) (he : e ≤ 1024)
    (hm : m ≤ 1024) (hh : h < 2 ^ 256) :
    osakaModexpGas b e m h = gasCost fork b m e h := by
  have hf' : fork ≥ Fork.fusaka := hf
  have hc := complexity_le fork hf b m hb hm
  have hi := iterations_le fork e h he hh
  unfold osakaModexpGas gasCost
  rw [osakaMultComplexity_eq fork hf b m hb hm, iterationCount_eq fork hf e h he hh]
  simp only [hf', if_true]
  try rw [show MIN_GAS = 500 from rfl]
  generalize complexity fork b m = c at *
  generalize iterations fork e h = it at *
  have hp : it * c ≤ (16 * 992 + 255) * (2 * 128 * 128) := Nat.mul_le_mul hi hc
  rw [Nat.mul_comm c it]
  simp only [maxU64]
  repeat' split
  all_goals omega

theorem osaka_gas_lt (fork : Fork) (hf : Spec.PostFusaka fork) (b e m h : Nat) (hb : b ≤ 1024) (he : e ≤ 1024)
    (hm : m ≤ 1024) (hh : h < 2 ^ 256) : gasCost fork b m e h < 2 ^ 64 := by
  have hf' : fork ≥ Fork.fusaka := hf
  have hc := complexity_le fork hf b m hb hm
  have hi := iterations_le fork e h he hh
  unfold gasCost
  simp only [hf', if_true]
  try rw [show MIN_GAS = 500 from rfl]
  generalize complexity fork b m = c at *
  generalize iterations fork e h = it at *
  have hp : c * it ≤ (2 * 128 * 128) * (16 * 992 + 255) := Nat.mul_le_mul hc hi
  omega

end FvModexp.Geth
