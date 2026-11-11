import FvModexp.Proofs.Common.ExpEven
import FvModexp.Proofs.Common.SubMod2NMath
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.modularInverseModPowerOfTwo` (go-bigmodexpfix nat.go:1287-1341): the machine-faithful run (agent infra)

For `n > 64` the Go code does
```go
z = z.make(numWords + 1)
zz := nat(nil).make(2 * numWords)
z.setWord(k0)                      // result DISCARDED: z keeps length numWords + 1
for i := uint(2); i < uint(numWords); i <<= 1 { … }
```
so the loop starts from the `numWords + 1` words of `z` with word 0 = `k0` and words `1..numWords` whatever `z.make`
left there (old contents of a reused `z`, zeros of a fresh one) — not from the value `k0` that the Nat model
`Exp.modularInverseModPowerOfTwo` uses. `modInvRun x n z0` is the faithful transcription with the initial value `z0`
(`z0 % B = k0`); `modInvRun_eq` shows the result does not depend on the high words: it is the unique inverse of `x`
below `2^n`, i.e. `Exp.modularInverseModPowerOfTwo x n`. (Harmless quirk of the Go code: Newton/Hensel only needs
`x·z ≡ 1 (mod 2^64)` at the start, and every round truncates.)
-/

namespace FvModexp.Exp

open Janus Janus.Arm64

/-- the `n > 64` branch of nat.go:1287-1341 from the initial `z` value `z0` (faithful: `z.setWord(k0)` discarded) -/
def modInvRun (x n z0 : Nat) : Nat :=
  let numWords := (n + 63) / 64
  let z := henselLoop x numWords 1 z0                       -- for i := 2; i < numWords; i <<= 1 { … }
  let zz := z * z % 2 ^ n                                   -- zz = zz.sqr(stk, z); zz = zz.trunc(zz, n)
  let zz := zz * (x % B ^ min numWords (nlen x)) % 2 ^ n    -- zz.mul(stk, zz, x[:min(numWords, lenX)]); trunc
  subMod2N (z * 2) zz n                                     -- z = z.lsh(z, 1); z.subMod2N(z, zz, n)

theorem henselLoop_step (x nw j z : Nat) (h : 2 ^ j < nw) :
    henselLoop x nw j z = henselLoop x nw (j + 1)
      (subMod2N (z * 2) (z * z % 2 ^ (2 ^ j * 64) * (x % B ^ min (2 ^ j) (nlen x)) % 2 ^ (2 ^ j * 64)) (2 ^ j * 64)) := by
  rw [henselLoop, dite_eq_left h]

theorem henselLoop_done (x nw j z : Nat) (h : ¬ 2 ^ j < nw) : henselLoop x nw j z = z := by
  rw [henselLoop, dite_eq_right h]

/-- inverses modulo `2^n` below `2^n` are unique -/
theorem inv_unique {x a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hxa : x * a % 2 ^ n = 1 % 2 ^ n)
    (hxb : x * b % 2 ^ n = 1 % 2 ^ n) : a = b := by
  have e1 : a * (x * b) % 2 ^ n = a := by
    rw [Nat.mul_mod, hxb, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt ha]
  have e2 : b * (x * a) % 2 ^ n = b := by
    rw [Nat.mul_mod, hxa, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt hb]
  have e3 : a * (x * b) = b * (x * a) := by
    rw [Nat.mul_left_comm, Nat.mul_comm a b, Nat.mul_left_comm b x a]
  calc a = a * (x * b) % 2 ^ n := e1.symm
    _ = b * (x * a) % 2 ^ n := by rw [e3]
    _ = b := e2

theorem modInvRun_spec (x n z0 : Nat) (hx : x % 2 = 1) (hn : 64 < n) (hz0 : z0 % B = newton 64 (x % B) % B) :
    modInvRun x n z0 < 2 ^ n ∧ x * modInvRun x n z0 % 2 ^ n = 1 % 2 ^ n := by
  have hx0 : x % B % 2 = 1 := by
    rw [B_def, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 64))]; exact hx
  have hxB : x % B < B := Nat.mod_lt _ B_pos
  have hN := newtonLoop_spec 64 (x % B) hxB (by omega) 64 0
    ((x % B + B - 1) % B) ((2 + B - x % B % B) % B) (by simp) (newton_init (x % B) hx0 hxB) (by
      have hB : B = 18446744073709551616 := B_eq
      have : (x % B + B - 1) % B = x % B - 1 := by rw [hB] at hxB ⊢; omega
      rw [this]; simp; omega)
  -- `x · z0 ≡ 1 (mod 2^64)`
  have h0 : x * z0 % 2 ^ (2 ^ 1 * 32) = 1 % 2 ^ (2 ^ 1 * 32) := by
    have hB64 : (2 : Nat) ^ (2 ^ 1 * 32) = B := by rw [B_def]
    rw [hB64, Nat.mul_mod, hz0, Nat.mul_mod (x % B), Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]
    have hN' : x % B * newtonLoop 64 0 ((x % B + B - 1) % B) ((2 + B - x % B % B) % B) % 2 ^ 64 = 1 % 2 ^ 64 := by
      simpa using hN
    unfold newton
    rw [← B_def] at hN'
    rw [Nat.mul_mod] at hN' ⊢; simp only [Nat.mod_mod] at hN' ⊢; exact hN'
  obtain ⟨j', hj', hj1, hz⟩ := henselLoop_spec x ((n + 63) / 64) ((n + 63) / 64) 1 z0 (by omega) (Nat.le_refl 1) h0
  refine ⟨(subMod2N_spec _ _ _).1, ?_⟩
  apply hensel_step x _ (2 ^ j' * 32) n _ _ hz
  · have : 2 ^ j' * 32 * 2 = 2 ^ j' * 64 := by omega
    omega
  · have hnw : n ≤ (n + 63) / 64 * 64 := by omega
    have hd : 2 ^ n ∣ 2 ^ ((n + 63) / 64 * 64) := Nat.pow_dvd_pow 2 hnw
    rw [← Nat.mod_mod_of_dvd _ hd, xs_mod, Nat.mod_mod_of_dvd _ hd]

/-- the machine-faithful run computes the model's value -/
theorem modInvRun_eq (x n z0 : Nat) (hx : x % 2 = 1) (hn : 64 < n) (hz0 : z0 % B = newton 64 (x % B) % B) :
    modInvRun x n z0 = modularInverseModPowerOfTwo x n := by
  obtain ⟨h1, h2⟩ := modInvRun_spec x n z0 hx hn hz0
  have h3 := modularInverseModPowerOfTwo_spec x n hx (by omega)
  have h4 : modularInverseModPowerOfTwo x n < 2 ^ n := by
    unfold modularInverseModPowerOfTwo; split
    · omega
    · exact (subMod2N_spec _ _ _).1
  exact inv_unique h1 h4 h2 h3

/-- the `x[:k]` prefix of a nat: its first `k ≤ l` words hold `X mod B^k` -/
theorem natVal_prefix (m : Memory) (p k l : Nat) (h : k ≤ l) : natVal m p k = natVal m p l % B ^ k := by
  have e := natVal_add m p k (l - k)
  rw [show k + (l - k) = l by omega] at e
  have hB : B ^ k = 2 ^ (64 * k) := by rw [B_def, ← Nat.pow_mul]
  rw [e, hB, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (natVal_lt m p k)]

end FvModexp.Exp
