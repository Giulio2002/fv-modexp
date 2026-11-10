import FvModexp.Proofs.Common.ExpMont
import FvModexp.Proofs.Common.ExpPow2
/-
  ExpEven: Nat-level models + correctness of
    nat.subMod2N                     nat.go:1726-1757
    nat.modularInverseModPowerOfTwo  nat.go:1287-1341
    nat.expNNEven                    nat.go:801-854   (CRT split m = 2^n · m2)
  Source: github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/nat.go.
  `nat.trunc(x, n)` (nat.go:530) is `x % 2^n`, `x[:k]` of a normalized `x` is `x % B^k`, `nat.lsh(x, s)` is
  `x * 2^s`, `nat.rsh(x, s)` is `x / 2^s`, `mul`/`sqr`/`add`/`sub` are the Nat operations (agent mathdiv).
-/
namespace FvModexp.Exp

/-! ### Int helpers -/

theorem int_dvd_of_mod_eq {a b P : Nat} (h : a % P = b % P) : (P : Int) ∣ (a : Int) - b := by
  have ha := Nat.div_add_mod a P
  have hb := Nat.div_add_mod b P
  refine ⟨((a / P : Nat) : Int) - ((b / P : Nat) : Int), ?_⟩
  have e1 : (a : Int) = P * ((a / P : Nat) : Int) + ((a % P : Nat) : Int) := by exact_mod_cast ha.symm
  have e2 : (b : Int) = P * ((b / P : Nat) : Int) + ((b % P : Nat) : Int) := by exact_mod_cast hb.symm
  rw [h] at e1
  rw [Int.mul_sub]; omega

theorem mod_eq_of_int_dvd {a b P : Nat} (h : (P : Int) ∣ (a : Int) - b) : a % P = b % P := by
  obtain ⟨q, hq⟩ := h
  have : ((a % P : Nat) : Int) = ((b % P : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_emod]
    have : (a : Int) = b + P * q := by omega
    rw [this, Int.add_mul_emod_self_left]
  exact_mod_cast this

/-! ### `nat.subMod2N` (nat.go:1726) -/

/-- `nat.subMod2N(x, y, n)` (nat.go:1726-1757). -/
def subMod2N (x y n : Nat) : Nat :=
  let x' := if n < bitLen x then x % 2 ^ n else x                 -- if x.bitLen() > n { x = trunc(x, n) }
  let y' := if n < bitLen y then y % 2 ^ n else y                 -- if y.bitLen() > n { y = trunc(y, n) }
  if y' ≤ x' then x' - y'                                         -- x.cmp(y) >= 0: z.sub(x, y)
  else
    let d := y' - x'                                              -- z = z.sub(y, x)
    let L := max (nlen d) ((n + 63) / 64)                         -- for len(z)*_W < n { z = append(z, 0) }
    (B ^ L - 1 - d) % 2 ^ n + 1                                   -- z[i] = ^z[i]; z = trunc(z, n); z.add(z, 1)

theorem lt_pow_of_bitLen {x n : Nat} (h : ¬ n < bitLen x) : x < 2 ^ n := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · exact Nat.two_pow_pos _
  · have := bitLen_lt hx
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))

theorem trunc_if_eq (x n : Nat) : (if n < bitLen x then x % 2 ^ n else x) = x % 2 ^ n := by
  split
  · rfl
  · rename_i h; exact (Nat.mod_eq_of_lt (lt_pow_of_bitLen h)).symm

theorem subMod2N_spec (x y n : Nat) :
    subMod2N x y n < 2 ^ n ∧ (subMod2N x y n + y) % 2 ^ n = x % 2 ^ n := by
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  unfold subMod2N
  simp only [trunc_if_eq]
  obtain ⟨a, ha⟩ : ∃ a, a = x % 2 ^ n := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = y % 2 ^ n := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have halt : a < 2 ^ n := ha ▸ Nat.mod_lt _ hP
  have hblt : b < 2 ^ n := hb ▸ Nat.mod_lt _ hP
  have hyb : (y : Nat) % 2 ^ n = b := hb.symm
  split
  · rename_i hle
    refine ⟨by omega, ?_⟩
    have hy := Nat.div_add_mod y (2 ^ n)
    rw [hyb] at hy
    rw [← hy, show a - b + (2 ^ n * (y / 2 ^ n) + b) = a + 2 ^ n * (y / 2 ^ n) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt halt]
  · rename_i hlt
    obtain ⟨d, hd⟩ : ∃ d, d = b - a := ⟨_, rfl⟩
    rw [← hd]
    have hd0 : 0 < d := by omega
    have hdP : d < 2 ^ n := by omega
    obtain ⟨W, hW⟩ : ∃ W, W = (n + 63) / 64 := ⟨_, rfl⟩
    have hnW : n ≤ 64 * W := by omega
    have hBW : B ^ W = 2 ^ n * 2 ^ (64 * W - n) := by
      rw [B_def, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
    have hdl : nlen d ≤ W := by
      apply nlen_le_iff.mpr
      rw [hBW]
      exact Nat.lt_of_lt_of_le hdP (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    rw [← hW, show max (nlen d) W = W by omega]
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ (64 * W - n) := ⟨_, rfl⟩
    have hQ1 : 1 ≤ Q := hQ ▸ Nat.two_pow_pos _
    rw [hBW, ← hQ]
    have e : 2 ^ n * Q - 1 - d = (2 ^ n - 1 - d) + 2 ^ n * (Q - 1) := by
      have : 2 ^ n * Q = 2 ^ n * (Q - 1) + 2 ^ n := by
        rw [Nat.mul_sub, Nat.mul_one]
        have : 2 ^ n ≤ 2 ^ n * Q := Nat.le_mul_of_pos_right _ hQ1
        omega
      omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, ?_⟩
    have hy := Nat.div_add_mod y (2 ^ n)
    rw [hyb] at hy
    rw [← hy, show 2 ^ n - 1 - d + 1 + (2 ^ n * (y / 2 ^ n) + b) = a + 2 ^ n * (y / 2 ^ n + 1) by
      rw [Nat.mul_add, Nat.mul_one]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt halt]

/-- Int form: `(P : Int) ∣ subMod2N x y n + y - x`. -/
theorem subMod2N_dvd (x y n : Nat) :
    ((2 ^ n : Nat) : Int) ∣ ((subMod2N x y n : Nat) : Int) + y - x := by
  have := int_dvd_of_mod_eq (subMod2N_spec x y n).2
  push_cast at this ⊢; exact this

/-! ### `nat.modularInverseModPowerOfTwo` (nat.go:1287) -/

/-- Hensel loop `for i := uint(2); i < uint(numWords); i <<= 1 { … }` (nat.go:1325-1332) with `i = 2^j`. -/
def henselLoop (x numWords : Nat) (j z : Nat) : Nat :=
  if h : 2 ^ j < numWords then
    let i := 2 ^ j
    let zz := z * z % 2 ^ (i * 64)                           -- zz = zz.sqr(stk, z); zz = zz.trunc(zz, i*_W)
    let zz := zz * (x % B ^ min i (nlen x)) % 2 ^ (i * 64)    -- zz = zz.mul(stk, zz, x[:min(i, lenX)]); trunc
    let z := subMod2N (z * 2) zz (i * 64)                     -- z = z.lsh(z, 1); z = z.subMod2N(z, zz, i*_W)
    henselLoop x numWords (j + 1) z
  else z
termination_by numWords - 2 ^ j
decreasing_by
  have := Nat.pow_lt_pow_succ (a := 2) (n := j) (by omega)
  omega

/-- `nat.modularInverseModPowerOfTwo(x, n)` (nat.go:1287-1341): `x^(-1) mod 2^n` for odd `x`, `n > 0`. -/
def modularInverseModPowerOfTwo (x n : Nat) : Nat :=
  let k0 := newton (min 64 n) (x % B)                         -- n0 := min(_W, n); Newton loop on x[0]
  if n ≤ 64 then k0 % 2 ^ n                                   -- k0 &= (1 << n) - 1; return z.setWord(k0)
  else
    let numWords := (n + 63) / 64
    let z := henselLoop x numWords 1 k0                       -- z.setWord(k0); loop from i = 2
    let zz := z * z % 2 ^ n                                   -- zz = zz.sqr(stk, z); zz = zz.trunc(zz, n)
    let zz := zz * (x % B ^ min numWords (nlen x)) % 2 ^ n    -- zz.mul(stk, zz, x[:min(numWords, lenX)]); trunc
    subMod2N (z * 2) zz n                                     -- z = z.lsh(z, 1); z.subMod2N(z, zz, n)

/-- One Newton/Hensel step: if `x*z ≡ 1 (mod 2^a)` and `b ≤ 2a`, the step result inverts `x` mod `2^b`. -/
theorem hensel_step (x z a b : Nat) (xs : Nat) (hxs : xs % 2 ^ b = x % 2 ^ b)
    (hz : x * z % 2 ^ a = 1 % 2 ^ a) (hab : b ≤ 2 * a) :
    x * subMod2N (z * 2) (z * z % 2 ^ b * xs % 2 ^ b) b % 2 ^ b = 1 % 2 ^ b := by
  apply mod_eq_of_int_dvd
  obtain ⟨q, hq⟩ := int_dvd_of_mod_eq hz
  have h1 := subMod2N_dvd (z * 2) (z * z % 2 ^ b * xs % 2 ^ b) b
  have h2 : ((2 ^ b : Nat) : Int) ∣ ((z * z % 2 ^ b * xs % 2 ^ b : Nat) : Int) - (z * z * x : Nat) := by
    apply int_dvd_of_mod_eq
    rw [Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, hxs, ← Nat.mul_mod]
  obtain ⟨q1, hq1⟩ := h1
  obtain ⟨q2, hq2⟩ := h2
  generalize subMod2N (z * 2) (z * z % 2 ^ b * xs % 2 ^ b) b = s at hq1
  generalize (z * z % 2 ^ b * xs % 2 ^ b : Nat) = t at hq1 hq2
  have hP : ((2 ^ (2 * a) : Nat) : Int) = ((2 ^ b : Nat) : Int) * ((2 ^ (2 * a - b) : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Nat.pow_add]; congr 2; omega
  have hPa : ((2 ^ (2 * a) : Nat) : Int) = ((2 ^ a : Nat) : Int) * ((2 ^ a : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Nat.pow_add]; congr 2; omega
  -- x*s - 1 = x*(s + t - 2z) - x*(t - z z x) + 2xz - x z z x - 1 ;  xz = 1 + 2^a q
  refine ⟨(x : Int) * q1 - x * q2 - ((2 ^ (2 * a - b) : Nat) : Int) * q * q, ?_⟩
  push_cast at hq1 hq2 hq hP hPa ⊢
  have hq' : (x : Int) * z = 1 + 2 ^ a * q := by omega
  rw [Int.mul_sub, Int.mul_sub]
  have e3 : (2 : Int) ^ b * (2 ^ (2 * a - b) * q * q) = (2 ^ a * q) * (2 ^ a * q) := by
    have : (2 : Int) ^ b * 2 ^ (2 * a - b) = 2 ^ a * 2 ^ a := by rw [← hP, hPa]
    grind
  rw [e3]
  have e1 : (2 : Int) ^ b * (x * q1) = x * (s + t - z * 2) := by rw [Int.mul_left_comm, ← hq1]
  have e2 : (2 : Int) ^ b * (x * q2) = x * (t - z * z * x) := by rw [Int.mul_left_comm, ← hq2]
  rw [e1, e2]
  have : (x : Int) * (z * z * x) = (x * z) * (x * z) := by grind
  rw [show (x : Int) * (s + t - z * 2) - x * (t - z * z * x) - 2 ^ a * q * (2 ^ a * q)
      = x * s - 2 * (x * z) + (x * z) * (x * z) - (2 ^ a * q) * (2 ^ a * q) by grind, hq']
  grind

theorem xs_mod (x i : Nat) : x % B ^ min i (nlen x) % 2 ^ (i * 64) = x % 2 ^ (i * 64) := by
  have hBi : B ^ i = 2 ^ (i * 64) := by rw [B_def, ← Nat.pow_mul, Nat.mul_comm]
  by_cases h : i ≤ nlen x
  · rw [Nat.min_eq_left h, hBi, Nat.mod_mod]
  · rw [Nat.min_eq_right (by omega), Nat.mod_eq_of_lt (lt_B_nlen x)]

theorem henselLoop_spec (x numWords : Nat) :
    ∀ fuel j z, numWords - 2 ^ j ≤ fuel → 1 ≤ j →
      x * z % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32) →
      ∃ j', numWords ≤ 2 ^ j' ∧ 1 ≤ j' ∧
        x * henselLoop x numWords j z % 2 ^ (2 ^ j' * 32) = 1 % 2 ^ (2 ^ j' * 32) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j z hf hj hz
    refine ⟨j, by omega, hj, ?_⟩
    unfold henselLoop; rw [dif_neg (by omega)]; exact hz
  | succ f ih =>
    intro j z hf hj hz
    unfold henselLoop
    by_cases hlt : 2 ^ j < numWords
    · rw [dif_pos hlt]
      simp only
      have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
      have hp0 : 0 < 2 ^ j := Nat.two_pow_pos j
      refine ih (j + 1) _ (by omega) (by omega) ?_
      have hb : 2 ^ (j + 1) * 32 = 2 ^ j * 64 := by rw [hp]; omega
      rw [hb]
      exact hensel_step x z (2 ^ j * 32) (2 ^ j * 64) _ (xs_mod x (2 ^ j)) hz (by omega)
    · refine ⟨j, by omega, hj, ?_⟩
      rw [dif_neg hlt]; exact hz

theorem newton_lt (n0 j t k : Nat) (hk : k < B) : newtonLoop n0 j t k < B := by
  induction j, t, k using newtonLoop.induct n0 with
  | case1 j t k h ih =>
    unfold newtonLoop; rw [dif_pos h]; exact ih (Nat.mod_lt _ B_pos)
  | case2 j t k h =>
    unfold newtonLoop; rw [dif_neg h]; exact hk

/-- **modularInverseModPowerOfTwo**: for odd `x` and `n > 0`, the result inverts `x` modulo `2^n`. -/
theorem modularInverseModPowerOfTwo_spec (x n : Nat) (hx : x % 2 = 1) (hn : 0 < n) :
    x * modularInverseModPowerOfTwo x n % 2 ^ n = 1 % 2 ^ n := by
  have hx0 : x % B % 2 = 1 := by
    rw [B_def, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 64))]; exact hx
  have hxB : x % B < B := Nat.mod_lt _ B_pos
  -- Newton phase: x[0] * k0 ≡ 1 mod 2^min(64,n)
  have hN := newtonLoop_spec (min 64 n) (x % B) hxB (by omega) (min 64 n) 0
    ((x % B + B - 1) % B) ((2 + B - x % B % B) % B) (by simp) (newton_init (x % B) hx0 hxB) (by
      have hB : B = 18446744073709551616 := B_eq
      have : (x % B + B - 1) % B = x % B - 1 := by rw [hB] at hxB ⊢; omega
      rw [this]; simp; omega)
  have hN' : x * newton (min 64 n) (x % B) % 2 ^ min 64 n = 1 % 2 ^ min 64 n := by
    unfold newton
    rw [Nat.mul_mod, ← Nat.mod_mod_of_dvd x (show 2 ^ min 64 n ∣ B by
      rw [B_def]; exact Nat.pow_dvd_pow 2 (by omega)), ← Nat.mul_mod]
    exact hN
  unfold modularInverseModPowerOfTwo
  simp only
  split
  · rename_i hle
    rw [Nat.min_eq_right hle] at hN' ⊢
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]; exact hN'
  · rename_i hgt
    rw [Nat.min_eq_left (by omega)] at hN' ⊢
    have h0 : x * newton 64 (x % B) % 2 ^ (2 ^ 1 * 32) = 1 % 2 ^ (2 ^ 1 * 32) := hN'
    obtain ⟨j', hj', hj1, hz⟩ := henselLoop_spec x ((n + 63) / 64) ((n + 63) / 64) 1 _
      (by omega) (Nat.le_refl 1) h0
    apply hensel_step x _ (2 ^ j' * 32) n _ _ hz
    · have : 2 ^ j' * 32 * 2 = 2 ^ j' * 64 := by omega
      omega
    · -- xs = x % B^min numWords (nlen x)
      have hnw : n ≤ (n + 63) / 64 * 64 := by omega
      have hd : 2 ^ n ∣ 2 ^ ((n + 63) / 64 * 64) := Nat.pow_dvd_pow 2 hnw
      rw [← Nat.mod_mod_of_dvd _ hd, xs_mod, Nat.mod_mod_of_dvd _ hd]

/-! ### `nat.expNNEven` (nat.go:801) -/

/-- `nat.expNNEven(x, y, m)` (nat.go:801-854), with the two recursive `expNN(…, false)` calls given by `rec`. -/
def expNNEven (rec : Nat → Nat → Nat → Nat) (x y m : Nat) : Nat :=
  let n := tz m                                    -- n := m.trailingZeroBits()
  let m1 := 2 ^ n                                  -- m1 = m1.lsh(natOne, n)
  let m2 := m / 2 ^ n                              -- m2 = m2.rsh(m, n)
  let z1 := rec x y m1                             -- z1 = z1.expNN(stk, x, y, m1, false)
  let z2 := rec x y m2                             -- z2 = z2.expNN(stk, x, y, m2, false)
  let z := z2                                      -- z = z.set(z2)
  let z1 := subMod2N z1 z2 n                       -- z1 = z1.subMod2N(z1, z2, n)
  let m2inv := modularInverseModPowerOfTwo m2 n    -- m2inv := m1.modularInverseModPowerOfTwo(stk, m2, n)
  let z2 := z1 * m2inv % 2 ^ n                     -- z2 = z2.mul(stk, z1, m2inv); z2 = z2.trunc(z2, n)
  z + z2 * m2                                      -- z = z.add(z, z1.mul(stk, z2, m2))

theorem crt_unique (a b P Q : Nat) (hco : Nat.Coprime P Q) (ha : a < P * Q) (hb : b < P * Q)
    (hP : a % P = b % P) (hQ : a % Q = b % Q) : a = b := by
  rcases Nat.le_total b a with h | h
  · have h1 : P ∣ a - b := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hP)
    have h2 : Q ∣ a - b := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hQ)
    have h3 := hco.mul_dvd_of_dvd_of_dvd h1 h2
    have h4 : a - b < P * Q := by omega
    have := Nat.eq_zero_of_dvd_of_lt h3 h4
    omega
  · have h1 : P ∣ b - a := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hP.symm)
    have h2 : Q ∣ b - a := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hQ.symm)
    have h3 := hco.mul_dvd_of_dvd_of_dvd h1 h2
    have h4 : b - a < P * Q := by omega
    have := Nat.eq_zero_of_dvd_of_lt h3 h4
    omega

/-- **expNNEven** is `x^y mod m` for even `m > 0`, given correct recursive calls (moduli `2^n` and the odd part). -/
theorem expNNEven_correct (rec : Nat → Nat → Nat → Nat) (x y m : Nat) (hm0 : 0 < m) (hme : m % 2 = 0)
    (hrec : ∀ m', 0 < m' → m' ∣ m → (m' % 2 = 1 ∨ ∃ k, m' = 2 ^ k) → rec x y m' = x ^ y % m') :
    expNNEven rec x y m = x ^ y % m := by
  obtain ⟨hms, hodd⟩ := tz_spec hm0
  unfold expNNEven
  simp only
  obtain ⟨n, hn⟩ : ∃ n, n = tz m := ⟨_, rfl⟩
  rw [← hn] at hms hodd ⊢
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m / 2 ^ n := ⟨_, rfl⟩
  rw [← hm2] at hms hodd ⊢
  have hn0 : 0 < n := by
    refine Nat.pos_of_ne_zero (fun h0 => ?_)
    rw [h0] at hms; simp at hms; omega
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  have hm2pos : 0 < m2 := by omega
  have hco : Nat.Coprime (2 ^ n) m2 := by
    refine Nat.Coprime.pow_left _ ?_
    show Nat.gcd 2 m2 = 1
    rw [Nat.gcd_rec, hodd]; rfl
  rw [hrec (2 ^ n) hP ⟨m2, hms⟩ (Or.inr ⟨n, rfl⟩),
    hrec m2 hm2pos ⟨2 ^ n, by rw [hms, Nat.mul_comm]⟩ (Or.inl hodd)]
  obtain ⟨z1, hz1⟩ : ∃ z1, z1 = x ^ y % 2 ^ n := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z2, z2 = x ^ y % m2 := ⟨_, rfl⟩
  rw [← hz1, ← hz2]
  have hz2lt : z2 < m2 := hz2 ▸ Nat.mod_lt _ hm2pos
  obtain ⟨s, hs⟩ : ∃ s, s = subMod2N z1 z2 n := ⟨_, rfl⟩
  have hsspec := subMod2N_spec z1 z2 n
  rw [← hs] at hsspec ⊢
  obtain ⟨v, hv⟩ : ∃ v, v = modularInverseModPowerOfTwo m2 n := ⟨_, rfl⟩
  have hvspec := modularInverseModPowerOfTwo_spec m2 n hodd hn0
  rw [← hv] at hvspec ⊢
  obtain ⟨p, hp⟩ : ∃ p, p = s * v % 2 ^ n := ⟨_, rfl⟩
  rw [← hp]
  have hplt : p < 2 ^ n := hp ▸ Nat.mod_lt _ hP
  -- z = z2 + p*m2 < m
  have hzlt : z2 + p * m2 < 2 ^ n * m2 := by
    have : (p + 1) * m2 ≤ 2 ^ n * m2 := Nat.mul_le_mul_right _ hplt
    grind
  have hpowlt : x ^ y % m < 2 ^ n * m2 := by rw [← hms]; exact Nat.mod_lt _ hm0
  apply crt_unique _ _ (2 ^ n) m2 hco hzlt hpowlt
  · -- mod 2^n: z2 + p*m2 ≡ z2 + s ≡ z1 ≡ x^y
    rw [Nat.mod_mod_of_dvd _ (⟨m2, hms⟩ : 2 ^ n ∣ m), ← hz1]
    have hz1lt : z1 < 2 ^ n := hz1 ▸ Nat.mod_lt _ hP
    rw [← Nat.mod_eq_of_lt hz1lt] at ⊢
    apply mod_eq_of_int_dvd
    have h1n : 1 % 2 ^ n = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    rw [h1n] at hvspec
    obtain ⟨a1, ha1⟩ := int_dvd_of_mod_eq (show p % 2 ^ n = (s * v) % 2 ^ n by rw [hp, Nat.mod_mod])
    obtain ⟨a2, ha2⟩ := int_dvd_of_mod_eq (show (m2 * v) % 2 ^ n = 1 % 2 ^ n by rw [hvspec, h1n])
    obtain ⟨a3, ha3⟩ := int_dvd_of_mod_eq hsspec.2
    refine ⟨a3 + m2 * a1 + s * a2, ?_⟩
    push_cast at ha1 ha2 ha3 ⊢
    rw [Int.mul_add, Int.mul_add, ← ha3, Int.mul_left_comm, ← ha1, Int.mul_left_comm, ← ha2]
    grind
  · -- mod m2
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz2lt, hz2]
    exact (Nat.mod_mod_of_dvd _ ⟨2 ^ n, by rw [hms, Nat.mul_comm]⟩).symm

end FvModexp.Exp
