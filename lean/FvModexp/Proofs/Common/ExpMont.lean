import FvModexp.Proofs.Common.ExpBase
/-
  ExpMont: Nat-level models of
    computeMontgomeryk0            nat.go:1273-1284
    nat.montgomery                 nat.go:188-215
  and their correctness (Montgomery / "Almost Montgomery Multiplication" invariants).
  Source: github.com/ethereum/go-bigmodexpfix@v0.0.0-20250911101455-f9e208c548ab/src/math/big/nat.go.
-/
namespace FvModexp.Exp

/-! ### `computeMontgomeryk0` (nat.go:1273) -/

/-- Newton–Raphson loop `for i := 1; i < n0; i <<= 1 { t *= t; k0 *= (t + 1) }` with `i = 2^j`, all Word-wrapping.
Shared by `computeMontgomeryk0` (n0 = 64) and `modularInverseModPowerOfTwo` (n0 = min(64,n)). -/
def newtonLoop (n0 : Nat) (j t k : Nat) : Nat :=
  if h : 2 ^ j < n0 then
    newtonLoop n0 (j + 1) (t * t % B) (k * ((t * t % B + 1) % B) % B)
  else k
termination_by n0 - 2 ^ j
decreasing_by
  have := Nat.pow_lt_pow_succ (a := 2) (n := j) (by omega)
  omega

/-- Newton start: `k0 := 2 - m0; t := m0 - 1` then the loop (value before the final negation). -/
def newton (n0 x0 : Nat) : Nat :=
  newtonLoop n0 0 ((x0 + B - 1) % B) ((2 + B - x0 % B) % B)

/-- `computeMontgomeryk0(m0)`: `k0 = -newton(64, m0)`. -/
def montK0 (m0 : Nat) : Nat := (B - newton 64 m0 % B) % B

theorem newton_exit (n0 a k t : Nat) (hn0 : n0 ≤ 64) (h1 : (a * k + t * t) % B = 1)
    (h2 : 2 ^ n0 ∣ t) : a * k % 2 ^ n0 = 1 % 2 ^ n0 := by
  have hd : 2 ^ n0 ∣ B := by
    unfold B; exact Nat.pow_dvd_pow 2 hn0
  have h3 : (a * k + t * t) % 2 ^ n0 = 1 % 2 ^ n0 := by
    rw [← Nat.mod_mod_of_dvd (a * k + t * t) hd, h1]
  obtain ⟨c, hc⟩ := h2
  have : t * t = 2 ^ n0 * (c * t) := by rw [hc]; grind
  rw [this, Nat.add_mul_mod_self_left] at h3
  exact h3

theorem newton_step (a k t : Nat) (h1 : (a * k + t * t) % B = 1) :
    (a * (k * ((t * t % B + 1) % B) % B) + (t * t % B) * (t * t % B)) % B = 1 := by
  have hB : (B : Int) = 18446744073709551616 := by rw [B_eq]; rfl
  obtain ⟨q, hq⟩ : ∃ q, a * k + t * t = 1 + B * q := by
    refine ⟨(a * k + t * t) / B, ?_⟩
    have := Nat.div_add_mod (a * k + t * t) B
    rw [h1] at this; omega
  obtain ⟨t', ht'⟩ : ∃ t', t' = t * t % B := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = (t' + 1) % B := ⟨_, rfl⟩
  obtain ⟨k', hk'⟩ : ∃ k', k' = k * s % B := ⟨_, rfl⟩
  have e1 := Nat.div_add_mod (t * t) B
  have e2 := Nat.div_add_mod (t' + 1) B
  have e3 := Nat.div_add_mod (k * s) B
  rw [← ht', ← hs, ← hk']
  rw [← ht'] at e1; rw [← hs] at e2; rw [← hk'] at e3
  have key : ((a * k' + t' * t' : Nat) : Int)
      = 1 + B * (((q : Int) - ((t * t / B : Nat) : Int)) * ((t' : Int) + 1)
          - (a : Int) * k * (((t' + 1) / B : Nat) : Int) - (a : Int) * ((k * s / B : Nat) : Int)) := by
    have hq' : ((a : Int) * k + (t : Int) * t) = 1 + B * q := by exact_mod_cast hq
    have e1' : (t : Int) * t = t' + B * ((t * t / B : Nat) : Int) := by have h := e1.symm; push_cast at h; omega
    have e2' : (t' : Int) + 1 = s + B * (((t' + 1) / B : Nat) : Int) := by have h := e2.symm; push_cast at h; omega
    have e3' : (k : Int) * s = k' + B * ((k * s / B : Nat) : Int) := by have h := e3.symm; push_cast at h; omega
    push_cast
    grind
  have hB' : (B : Int) = 18446744073709551616 := hB
  simp only [B_eq] at key ⊢
  omega

theorem newtonLoop_spec (n0 a : Nat) (haB : a < B) (hn0 : n0 ≤ 64) :
    ∀ (fuel j t k : Nat), n0 - 2 ^ j ≤ fuel →
      (a * k + t * t) % B = 1 → 2 ^ min (2 ^ j) 64 ∣ t →
      a * newtonLoop n0 j t k % 2 ^ n0 = 1 % 2 ^ n0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro j t k hf h1 h2
    unfold newtonLoop
    rw [dif_neg (by omega)]
    refine newton_exit n0 a k t hn0 h1 ?_
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) h2
  | succ f ih =>
    intro j t k hf h1 h2
    by_cases hlt : 2 ^ j < n0
    · unfold newtonLoop
      rw [dif_pos hlt]
      have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
      have hp0 : 0 < 2 ^ j := Nat.two_pow_pos _
      refine ih (j + 1) _ _ (by omega) (newton_step a k t h1) ?_
      have hdB : 2 ^ min (2 ^ (j + 1)) 64 ∣ B := by
        unfold B; exact Nat.pow_dvd_pow 2 (by omega)
      rw [Nat.dvd_mod_iff hdB]
      have : 2 ^ (2 * min (2 ^ j) 64) ∣ t * t := by
        rw [Nat.two_mul, Nat.pow_add]; exact Nat.mul_dvd_mul h2 h2
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) this
    · unfold newtonLoop
      rw [dif_neg hlt]
      refine newton_exit n0 a k t hn0 h1 ?_
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) h2

theorem newton_init (a : Nat) (ha : a % 2 = 1) (haB : a < B) :
    (a * ((2 + B - a % B) % B) + ((a + B - 1) % B) * ((a + B - 1) % B)) % B = 1 := by
  have hB : B = 18446744073709551616 := B_eq
  have hmod : a % B = a := Nat.mod_eq_of_lt haB
  rw [hmod]
  rcases Nat.lt_or_ge a 2 with h | h
  · have : a = 1 := by omega
    subst this
    rw [B_eq]
  · have ht : (a + B - 1) % B = a - 1 := by rw [hB] at haB ⊢; omega
    have hk : (2 + B - a) % B = B + 2 - a := by rw [hB] at haB ⊢; omega
    rw [ht, hk]
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hc : B + 2 - (a' + 1) = B + 1 - a' := by omega
    rw [hc]
    have : (a' + 1) * (B + 1 - a') + a' * a' = 1 + (a' + 1) * B := by
      have : B + 1 - a' + a' = B + 1 := by omega
      grind
    rw [this, Nat.add_mul_mod_self_right]
    rw [B_eq]

theorem montK0_spec (m0 : Nat) (hm : m0 % 2 = 1) (hmB : m0 < B) : (montK0 m0 * m0 + 1) % B = 0 := by
  have hB : B = 18446744073709551616 := B_eq
  unfold montK0 newton
  have hspec := newtonLoop_spec 64 m0 hmB (by omega) 64 0 ((m0 + B - 1) % B) ((2 + B - m0 % B) % B)
    (by simp) (newton_init m0 hm hmB) (by
      have : (m0 + B - 1) % B = m0 - 1 := by rw [hB] at hmB ⊢; omega
      rw [this]; simp; omega)
  have h2 : (2:Nat) ^ 64 = B := by rw [B_eq]
  rw [h2] at hspec
  rw [show 1 % B = 1 by rw [B_eq]] at hspec
  obtain ⟨K, hK⟩ : ∃ K, K = newtonLoop 64 0 ((m0 + B - 1) % B) ((2 + B - m0 % B) % B) := ⟨_, rfl⟩
  rw [← hK] at hspec ⊢
  have hr : m0 * (K % B) % B = 1 := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]; exact hspec
  obtain ⟨q, hq⟩ : ∃ q, m0 * (K % B) = 1 + B * q := by
    refine ⟨m0 * (K % B) / B, ?_⟩
    have := Nat.div_add_mod (m0 * (K % B)) B
    rw [hr] at this; omega
  have hrlt : K % B < B := Nat.mod_lt _ B_pos
  have hr0 : 0 < K % B := by
    refine Nat.pos_of_ne_zero (fun h0 => ?_)
    rw [h0] at hq; omega
  have hc : (B - K % B) % B = B - K % B := Nat.mod_eq_of_lt (by omega)
  rw [hc]
  have key : ((((B - K % B) * m0 + 1 : Nat)) : Int) = B * ((m0 : Int) - q) := by
    have h1 : ((B - K % B : Nat) : Int) = B - ((K % B : Nat) : Int) := by omega
    have hq' : (m0 : Int) * ((K % B : Nat) : Int) = 1 + B * q := by exact_mod_cast hq
    push_cast [h1]
    grind
  rw [hB] at key ⊢
  omega

/-! ### `nat.montgomery` (nat.go:188-215)

`z` is a `2n`-limb array modelled by the Nat it denotes; window / limb access via div/mod. -/

/-- `z[i:i+n]` -/
def win (Z i n : Nat) : Nat := Z / B ^ i % B ^ n

/-- `z[i:i+n] = v` (other limbs untouched; `v < B^n`). -/
def setWin (Z i n v : Nat) : Nat := Z % B ^ i + v * B ^ i + Z / B ^ (i + n) * B ^ (i + n)

/-- Loop body (i-th iteration), nat.go:198-211.  State `(z, c)`. -/
def montStep (n x m k d i : Nat) (st : Nat × Nat) : Nat × Nat :=
  let Z := st.1
  let c := st.2
  let a1 := win Z i n + x * d                  -- addMulVVWW(z[i:n+i], z[i:n+i], x, d, 0)
  let c2 := a1 / B ^ n
  let Z1 := setWin Z i n (a1 % B ^ n)
  let t := wd Z1 i * k % B                     -- t := z[i] * k
  let a2 := win Z1 i n + m * t                 -- addMulVVWW(z[i:n+i], z[i:n+i], m, t, 0)
  let c3 := a2 / B ^ n
  let Z2 := setWin Z1 i n (a2 % B ^ n)
  let cx := (c + c2) % B
  let cy := (cx + c3) % B
  let Z3 := setWin Z2 (n + i) 1 cy             -- z[n+i] = cy
  (Z3, if cx < c2 ∨ cy < c3 then 1 else 0)

/-- State after `j` loop iterations (`z = z.make(2n); clear(z); c = 0` initially). -/
def montIter (n x y m k : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | j + 1 => montStep n x m k (wd y j) j (montIter n x y m k j)

/-- `nat.montgomery(x, y, m, k, n)`: returns `z[:n]` (nat.go:212-218). -/
def montgomery (n x y m k : Nat) : Nat :=
  let st := montIter n x y m k n
  let hi := win st.1 n n                        -- z[n:2n]
  if st.2 ≠ 0 then (hi + B ^ n - m) % B ^ n     -- subVV(z[:n], z[n:], m)
  else hi                                       -- copy(z[:n], z[n:])

theorem setWin_clear (V i n v : Nat) (hV : V < B ^ n) :
    setWin (B ^ i * V) i n v = v * B ^ i ∧ win (B ^ i * V) i n = V := by
  have hBi : 0 < B ^ i := Nat.pow_pos B_pos
  have hBn : 0 < B ^ n := Nat.pow_pos B_pos
  have h1 : B ^ i * V % B ^ i = 0 := Nat.mul_mod_right _ _
  have h2 : B ^ i * V / B ^ i = V := Nat.mul_div_cancel_left _ hBi
  have h3 : B ^ i * V / B ^ (i + n) = 0 := by
    rw [Nat.pow_add, Nat.div_eq_zero_iff]
    right
    have h := Nat.mul_lt_mul_of_pos_left hV hBi
    exact h
  constructor
  · unfold setWin; rw [h1, h3]; simp
  · unfold win; rw [h2]; exact Nat.mod_eq_of_lt hV

theorem setWin_top (Z j v : Nat) (hZ : Z < B ^ j) : setWin Z j 1 v = Z + v * B ^ j := by
  unfold setWin
  rw [Nat.mod_eq_of_lt hZ, Nat.div_eq_of_lt (a := Z) (b := B ^ (j + 1))]
  · simp
  · rw [Nat.pow_succ]; exact Nat.lt_of_lt_of_le hZ (Nat.le_mul_of_pos_right _ B_pos)

theorem kfac (k m B' : Nat) (hk : (k * m + 1) % B' = 0) (s : Nat) :
    (s + m * (s * k % B')) % B' = 0 := by
  have h1 : (s + m * (s * k % B')) % B' = (s + m * (s * k)) % B' := by
    rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
  rw [h1]
  have : s + m * (s * k) = s * (k * m + 1) := by grind
  rw [this, Nat.mul_mod, hk]; simp

theorem carry_lemma (c c2 c3 : Nat) (hc : c ≤ 1) (h2 : c2 < B) (h3 : c3 < B) :
    c + c2 + c3 = (((c + c2) % B) + c3) % B
      + (if (c + c2) % B < c2 ∨ ((c + c2) % B + c3) % B < c3 then 1 else 0) * B := by
  simp only [B_eq] at h2 h3 ⊢
  split <;> omega

/-- Loop invariant of `nat.montgomery` after `i` iterations. -/
def MInv (n x y m i : Nat) (st : Nat × Nat) : Prop :=
  ∃ V Q, st.1 = B ^ i * V ∧ V < B ^ n ∧ Q < B ^ i ∧ st.2 ≤ 1 ∧
    B ^ i * V + st.2 * B ^ (n + i) = x * (y % B ^ i) + m * Q

theorem mac_lt (R Bw V x d : Nat) (hV : V < R) (hx : x < R) (hd : d < Bw) : V + x * d < R * Bw := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, Bw = e + 1 := ⟨Bw - 1, by omega⟩
  have : x * d ≤ r * e := Nat.mul_le_mul (by omega) (by omega)
  grind

theorem mont_alg (Bi Bn Bw V x d S1 c2 c S2 c3 cy c' t Q Yl Yl' m : Nat)
    (eq0 : Bi * V + c * (Bn * Bi) = x * Yl + m * Q)
    (ha1 : V + x * d = c2 * Bn + S1) (ha2 : S1 + m * t = c3 * Bn + S2)
    (hcar : c + c2 + c3 = cy + c' * Bw) (hy : Yl' = Yl + Bi * d) :
    Bi * S2 + cy * (Bn * Bi) + c' * (Bn * Bi * Bw) = x * Yl' + m * (Q + t * Bi) := by
  subst hy
  grind

theorem mont_fin (Bi P Bw S2q S2 cy c' x Yl' m Q t : Nat)
    (this : Bi * S2 + cy * (P * Bw * Bi) + c' * (P * Bw * Bi * Bw) = x * Yl' + m * (Q + t * Bi))
    (hS2 : S2 = Bw * S2q) :
    Bi * Bw * (S2q + cy * P) + c' * (P * Bw * Bi * Bw) = x * Yl' + m * (Q + t * Bi) := by
  subst hS2; rw [← this]; grind

theorem mont_lt1 (P Bw S2q cy : Nat) (h1 : S2q < P) (hcy : cy < Bw) : S2q + cy * P < P * Bw := by
  have h2 : (cy + 1) * P ≤ Bw * P := Nat.mul_le_mul_right _ hcy
  grind

theorem mont_lt2 (Bi Bw Q t : Nat) (hQ : Q < Bi) (htB : t < Bw) : Q + t * Bi < Bi * Bw := by
  have h2 : (t + 1) * Bi ≤ Bw * Bi := Nat.mul_le_mul_right _ htB
  grind

theorem montStep_inv (n x y m k i : Nat) (hn : 1 ≤ n) (hx : x < B ^ n) (hm : m < B ^ n)
    (hk : (k * m + 1) % B = 0)
    (st : Nat × Nat) (h : MInv n x y m i st) :
    MInv n x y m (i + 1) (montStep n x m k (wd y i) i st) := by
  obtain ⟨Z, c⟩ := st
  obtain ⟨V, Q, hZ, hV, hQ, hc, heq⟩ := h
  simp only at hZ hc heq
  subst hZ
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hBi : 0 < B ^ i := Nat.pow_pos B_pos
  have hBn : 0 < B ^ n := Nat.pow_pos B_pos
  have hBn1 : B ^ n = B ^ n' * B := by rw [hn']; exact Nat.pow_succ ..
  obtain ⟨d, hd⟩ : ∃ d, d = wd y i := ⟨_, rfl⟩
  have hdB : d < B := by rw [hd]; exact wd_lt y i
  obtain ⟨c2, hc2⟩ : ∃ c2, c2 = (V + x * d) / B ^ n := ⟨_, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = (V + x * d) % B ^ n := ⟨_, rfl⟩
  have hS1lt : S1 < B ^ n := by rw [hS1]; exact Nat.mod_lt _ hBn
  have hc2lt : c2 < B := by
    rw [hc2, Nat.div_lt_iff_lt_mul hBn, Nat.mul_comm B]
    exact mac_lt (B ^ n) B V x d hV hx hdB
  have ha1 : V + x * d = c2 * B ^ n + S1 := by
    rw [hc2, hS1]; have := Nat.div_add_mod (V + x * d) (B ^ n); grind
  have hs1 := setWin_clear V i n S1 hV
  obtain ⟨t, ht⟩ : ∃ t, t = S1 % B * k % B := ⟨_, rfl⟩
  have htB : t < B := by rw [ht]; exact Nat.mod_lt _ B_pos
  have hwd1 : wd (B ^ i * S1) i = S1 % B := by
    unfold wd; rw [Nat.mul_div_cancel_left _ hBi]
  obtain ⟨c3, hc3⟩ : ∃ c3, c3 = (S1 + m * t) / B ^ n := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = (S1 + m * t) % B ^ n := ⟨_, rfl⟩
  have hS2lt : S2 < B ^ n := by rw [hS2]; exact Nat.mod_lt _ hBn
  have hc3lt : c3 < B := by
    rw [hc3, Nat.div_lt_iff_lt_mul hBn, Nat.mul_comm B]
    exact mac_lt (B ^ n) B S1 m t hS1lt hm htB
  have ha2 : S1 + m * t = c3 * B ^ n + S2 := by
    rw [hc3, hS2]; have := Nat.div_add_mod (S1 + m * t) (B ^ n); grind
  have hS2mod : S2 % B = 0 := by
    have hdvd : B ∣ B ^ n := ⟨B ^ n', by rw [hBn1, Nat.mul_comm]⟩
    rw [hS2, Nat.mod_mod_of_dvd _ hdvd, ← Nat.mod_add_mod, ht]
    exact kfac k m B hk (S1 % B)
  have hsA := setWin_clear S1 i n S2 hS1lt
  simp only [montStep]
  rw [← hd, hs1.2, ← hS1, hs1.1, Nat.mul_comm S1 (B ^ i), hsA.2, hwd1, ← ht, ← hc2, ← hc3, ← hS2, hsA.1]
  obtain ⟨cy, hcy⟩ : ∃ cy, cy = ((c + c2) % B + c3) % B := ⟨_, rfl⟩
  rw [← hcy]
  obtain ⟨c', hc'⟩ : ∃ c', c' = if (c + c2) % B < c2 ∨ cy < c3 then 1 else 0 := ⟨_, rfl⟩
  rw [← hc']
  have hcar : c + c2 + c3 = cy + c' * B := by
    have := carry_lemma c c2 c3 hc hc2lt hc3lt
    rw [← hcy, ← hc'] at this; exact this
  have hcy_lt : cy < B := by rw [hcy]; exact Nat.mod_lt _ B_pos
  have hc'le : c' ≤ 1 := by rw [hc']; split <;> omega
  have hZ2 : S2 * B ^ i < B ^ (n + i) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hS2lt hBi
  rw [setWin_top _ _ _ hZ2]
  have hBpow : B ^ (n + i) = B ^ n' * B * B ^ i := by rw [Nat.pow_add, hBn1]
  have hBpow1 : B ^ (n + (i + 1)) = B ^ n' * B * B ^ i * B := by
    rw [← Nat.add_assoc, Nat.pow_succ, hBpow]
  have hBi1 : B ^ (i + 1) = B ^ i * B := Nat.pow_succ ..
  have hS2eq : S2 = B * (S2 / B) := by have := Nat.div_add_mod S2 B; omega
  have hy : y % B ^ (i + 1) = y % B ^ i + B ^ i * d := by
    rw [hBi1, Nat.mod_mul, hd]; rfl
  have hP : 0 < B ^ n' := Nat.pow_pos B_pos
  refine ⟨S2 / B + cy * B ^ n', Q + t * B ^ i, ?_, ?_, ?_, hc'le, ?_⟩
  · simp only
    rw [hBpow, hBi1]
    have : S2 * B ^ i = B ^ i * (B * (S2 / B)) := by rw [← hS2eq]; grind
    rw [this]; grind
  · have h1 : S2 / B < B ^ n' := by
      rw [Nat.div_lt_iff_lt_mul B_pos, ← hBn1]; exact hS2lt
    rw [hBn1]; exact mont_lt1 _ _ _ _ h1 hcy_lt
  · rw [hBi1]; exact mont_lt2 _ _ _ _ hQ htB
  · simp only
    have eq0 : B ^ i * V + c * (B ^ n * B ^ i) = x * (y % B ^ i) + m * Q := by
      rw [Nat.pow_add] at heq; exact heq
    have := mont_alg (B ^ i) (B ^ n) B V x d S1 c2 c S2 c3 cy c' t Q (y % B ^ i) (y % B ^ (i + 1)) m
      eq0 ha1 ha2 hcar hy
    rw [hBn1] at this
    have := mont_fin (B ^ i) (B ^ n') B (S2 / B) S2 cy c' x (y % B ^ (i + 1)) m Q t this hS2eq
    rw [hBpow1, hBi1]
    exact this

theorem montIter_inv (n x y m k : Nat) (hn : 1 ≤ n) (hx : x < B ^ n) (hm : m < B ^ n)
    (hk : (k * m + 1) % B = 0) : ∀ j, MInv n x y m j (montIter n x y m k j) := by
  intro j
  induction j with
  | zero =>
    refine ⟨0, 0, ?_, Nat.pow_pos B_pos, Nat.pow_pos B_pos, by simp [montIter], ?_⟩
    · simp [montIter]
    · simp [montIter, Nat.mod_one]
  | succ j ih =>
    exact montStep_inv n x y m k j hn hx hm hk _ ih

/-- **Montgomery invariants**: for `x, y < B^n`, `m < B^n` and `k*m ≡ -1 (mod B)`, the result of
`nat.montgomery` is `T` (or `T - m` if `T ≥ B^n`) where `T * B^n = x*y + Q*m` for some `Q < B^n`. -/
theorem montgomery_spec (n x y m k : Nat) (hn : 1 ≤ n) (hx : x < B ^ n) (hy : y < B ^ n)
    (hm : m < B ^ n) (hk : (k * m + 1) % B = 0) :
    ∃ Q T, Q < B ^ n ∧ T * B ^ n = x * y + Q * m ∧ T < B ^ n + m ∧
      montgomery n x y m k = if B ^ n ≤ T then T - m else T := by
  obtain ⟨V, Q, hZ, hV, hQ, hc, heq⟩ := montIter_inv n x y m k hn hx hm hk n
  rw [Nat.mod_eq_of_lt hy] at heq
  have hBn : 0 < B ^ n := Nat.pow_pos B_pos
  have hT : (V + (montIter n x y m k n).2 * B ^ n) * B ^ n = x * y + Q * m := by
    rw [Nat.pow_add] at heq; rw [← Nat.mul_comm Q m] at *; grind
  have hTlt : V + (montIter n x y m k n).2 * B ^ n < B ^ n + m := by
    have h1 : x * y < B ^ n * B ^ n := Nat.mul_lt_mul'' hx hy
    have h2 : Q * m ≤ B ^ n * m := Nat.mul_le_mul_right _ (Nat.le_of_lt hQ)
    have h3 : (V + (montIter n x y m k n).2 * B ^ n) * B ^ n < (B ^ n + m) * B ^ n := by
      rw [hT]; grind
    exact Nat.lt_of_mul_lt_mul_right h3
  refine ⟨Q, V + (montIter n x y m k n).2 * B ^ n, hQ, hT, hTlt, ?_⟩
  unfold montgomery
  simp only
  have hw : win (montIter n x y m k n).1 n n = V := by
    rw [hZ]; exact (setWin_clear V n n 0 hV).2
  rw [hw]
  generalize (montIter n x y m k n).2 = c at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
  · subst h0; simp; intro h; exact absurd h (Nat.not_le.mpr hV)
  · subst h1
    have hVm : V < m := by omega
    have hmle : m ≤ B ^ n := Nat.le_of_lt hm
    simp only [ne_eq, Nat.one_ne_zero, not_false_eq_true, if_true, Nat.one_mul]
    rw [if_pos (by omega)]
    have : V + B ^ n - m < B ^ n := by omega
    rw [Nat.mod_eq_of_lt this]

end FvModexp.Exp
