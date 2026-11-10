import FvModexp.Proofs.Common.ExpWindow
/-
  ExpPow2: power-of-two modulus  m = 2^L
    buildPrecomputationWindowModPower2   nat.go:856-899
    expNNPowerOfTwo                      nat.go:906-973
    expNNPowerOfTwoWindowSize4 / 2       nat.go:975-1127 / 1129-1285
  and the correctness proofs.
-/
namespace FvModexp.Exp

/-! ### Euler-type lemma for 2-power moduli -/

theorem odd_pow_two_pow (x : Nat) (hx : x % 2 = 1) : ∀ k, x ^ (2 ^ k) % 2 ^ (k + 1) = 1 := by
  intro k
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    obtain ⟨s, hs⟩ : ∃ s, x ^ (2 ^ k) = 2 ^ (k + 1) * s + 1 := by
      refine ⟨x ^ (2 ^ k) / 2 ^ (k + 1), ?_⟩
      have := Nat.div_add_mod (x ^ (2 ^ k)) (2 ^ (k + 1))
      rw [ih] at this; omega
    have h1 : x ^ (2 ^ (k + 1)) = (x ^ (2 ^ k)) * (x ^ (2 ^ k)) := by
      rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
    rw [h1, hs]
    obtain ⟨c, hc⟩ : ∃ c, c = 2 ^ k := ⟨_, rfl⟩
    have e1 : 2 ^ (k + 1) = 2 * c := by rw [Nat.pow_succ, hc]; grind
    have e2 : 2 ^ (k + 1 + 1) = 4 * c := by rw [Nat.pow_succ, Nat.pow_succ, hc]; grind
    have : (2 ^ (k + 1) * s + 1) * (2 ^ (k + 1) * s + 1) = 1 + 2 ^ (k + 1 + 1) * (c * s * s + s) := by
      rw [e1, e2]; grind
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

theorem pow_mod_phi (x L a b : Nat) (hx : x % 2 = 1) (hL : 1 ≤ L)
    (h : a % 2 ^ (L - 1) = b % 2 ^ (L - 1)) : x ^ a % 2 ^ L = x ^ b % 2 ^ L := by
  have key : ∀ c, x ^ c % 2 ^ L = x ^ (c % 2 ^ (L - 1)) % 2 ^ L := by
    intro c
    have h1 : x ^ (2 ^ (L - 1)) % 2 ^ L = 1 := by
      have := odd_pow_two_pow x hx (L - 1)
      rwa [show L - 1 + 1 = L by omega] at this
    have e : x ^ c = (x ^ (2 ^ (L - 1))) ^ (c / 2 ^ (L - 1)) * x ^ (c % 2 ^ (L - 1)) := by
      rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
    have h2 : 1 % 2 ^ L = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    rw [e, Nat.mul_mod, Nat.pow_mod, h1, Nat.one_pow, h2, Nat.one_mul, Nat.mod_mod]
  rw [key a, key b, h]

/-! ### buildPrecomputationWindowModPower2 (nat.go:856) -/

/-- `powers[i]`: `powers[0]=1`, `powers[1]=trunc(x)`, `powers[2j]=trunc(sqr(powers[j]))`,
`powers[2j+1]=trunc(powers[2j]*powers[1])`. -/
def p2Pow (L x : Nat) (i : Nat) : Nat :=
  if h0 : i = 0 then 1
  else if h1 : i = 1 then x % 2 ^ L
  else if i % 2 = 0 then p2Pow L x (i / 2) * p2Pow L x (i / 2) % 2 ^ L
  else p2Pow L x (i - 1) * (x % 2 ^ L) % 2 ^ L
termination_by i
decreasing_by all_goals omega

/-- `z` represents `x^e mod 2^L` (reduced). -/
def PRep (L x z e : Nat) : Prop := z < 2 ^ L ∧ z = x ^ e % 2 ^ L

theorem p2Pow_rep (L x : Nat) (hL : 1 ≤ L) : ∀ i, PRep L x (p2Pow L x i) i := by
  have h2L : 1 < 2 ^ L := Nat.one_lt_two_pow (by omega)
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    unfold p2Pow
    by_cases h0 : i = 0
    · subst h0; simp [PRep, Nat.mod_eq_of_lt h2L]; omega
    · by_cases h1 : i = 1
      · subst h1; simp [PRep]; exact Nat.mod_lt _ (by omega)
      · simp only [h0, h1, dite_false]
        by_cases he : i % 2 = 0
        · simp only [he, if_true]
          have := ih (i / 2) (by omega)
          refine ⟨Nat.mod_lt _ (by omega), ?_⟩
          rw [this.2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_add]
          congr 2; omega
        · simp only [he, if_false]
          have := ih (i - 1) (by omega)
          refine ⟨Nat.mod_lt _ (by omega), ?_⟩
          rw [this.2, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_succ]
          congr 2; omega

theorem iterSq_rep (L x : Nat) (hL : 1 ≤ L) :
    ∀ (j z e : Nat), PRep L x z e → PRep L x (iter (fun z => z * z % 2 ^ L) j z) (e * 2 ^ j) := by
  intro j
  induction j with
  | zero => intro z e h; simpa [iter] using h
  | succ j ih =>
    intro z e h
    have h1 : PRep L x (z * z % 2 ^ L) (e + e) := by
      refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
      rw [h.2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_add]
    have := ih _ _ h1
    simp only [iter]
    have e2 : (e + e) * 2 ^ j = e * 2 ^ (j + 1) := by rw [Nat.pow_succ]; grind
    rwa [e2] at this

theorem p2step_rep (L x w : Nat) (hL : 1 ≤ L) :
    StepOk w (PRep L x)
      (fun z d => iter (fun z => z * z % 2 ^ L) w z * p2Pow L x d % 2 ^ L) := by
  intro z e d _ hz
  have h1 := iterSq_rep L x hL w z e hz
  have h2 := p2Pow_rep L x hL d
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
  show iter (fun z => z * z % 2 ^ L) w z * p2Pow L x d % 2 ^ L = _
  rw [Nat.mul_mod, h1.2, h2.2, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_add]

theorem mod_succ (y i : Nat) : y % B ^ (i + 1) = wd y i * B ^ i + y % B ^ i := by
  unfold wd
  rw [Nat.pow_succ, Nat.mod_mul]; grind

/-- `for yi == 0 { if i == 0 { return 1 }; i--; yi = y[i] }` (nat.go:1033-1043). `none` = `return 1`. -/
def skipZero (y : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, yi => if yi ≠ 0 then some (0, yi) else none
  | i + 1, yi => if yi ≠ 0 then some (i + 1, yi) else skipZero y i (wd y i)

theorem skipZero_spec (y : Nat) : ∀ i yi, yi < B →
    (match skipZero y i yi with
     | none => yi * B ^ i + y % B ^ i = 0
     | some (i', yi') => yi' ≠ 0 ∧ yi' < B ∧ yi' * B ^ i' + y % B ^ i' = yi * B ^ i + y % B ^ i) := by
  intro i
  induction i with
  | zero =>
    intro yi hyi
    unfold skipZero
    by_cases h : yi ≠ 0
    · simp [h, hyi]
    · simp only [h, if_false]; simp at h; subst h; simp [Nat.mod_one]
  | succ i ih =>
    intro yi hyi
    unfold skipZero
    by_cases h : yi ≠ 0
    · simp [h, hyi]
    · simp only [h, if_false]
      simp at h; subst h
      have := ih (wd y i) (wd_lt y i)
      have e := mod_succ y i
      generalize skipZero y i (wd y i) = r at this
      match r, this with
      | none, h => simp only; grind
      | some (i', yi'), h => simp only at h ⊢; grind

/-- `expNNPowerOfTwoWindowSize{2,4}` (nat.go:975-1127, 1129-1285) with window `w`, `m = 2^L`, `x` odd. -/
def p2win (w L x y : Nat) : Nat :=
  let tbl := p2Pow L x                                       -- buildPrecomputationWindowModPower2
  let step := fun z d => iter (fun z => z * z % 2 ^ L) w z * tbl d % 2 ^ L
  let mtop := (L - 2) / 64
  let mbits := (L - 1) % 64
  let i0 := min (nlen y - 1) mtop                            -- i := len(y)-1; if i > mtop { i = mtop }
  let yi0 := if i0 = mtop then (if mbits ≠ 0 then wd y i0 % 2 ^ mbits else wd y i0) else wd y i0
  match skipZero y i0 yi0 with
  | none => 1
  | some (i, yi) => winRun w step tbl y i yi

theorem p2win_correct (w L x y : Nat) (hw : w = 2 ∨ w = 4) (hx : x % 2 = 1) (hy : 0 < y)
    (hL : 2 ≤ L) : p2win w L x y = x ^ y % 2 ^ L := by
  have hw0 : 0 < w := by omega
  have hK : 64 / w * w = 64 := by rcases hw with rfl | rfl <;> decide
  have hw64 : w ≤ 64 := by omega
  obtain ⟨q, hq⟩ : ∃ q, q = (L - 2) / 64 := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr, rr = (L - 2) % 64 + 1 := ⟨_, rfl⟩
  have hLq : L - 1 = 64 * q + rr := by omega
  have hrr1 : 1 ≤ rr ∧ rr ≤ 64 := by omega
  have hmb : (L - 1) % 64 = rr % 64 := by omega
  obtain ⟨T, hT⟩ : ∃ T, T = 2 ^ (L - 1) := ⟨_, rfl⟩
  have hTB : T = B ^ q * 2 ^ rr := by
    rw [hT, hLq, Nat.pow_add, B_def, ← Nat.pow_mul]
  have hdvd : 2 ^ rr ∣ B := by rw [B_def]; exact Nat.pow_dvd_pow 2 hrr1.2
  -- masked word
  have hmask : (if (L - 1) % 64 ≠ 0 then wd y q % 2 ^ ((L - 1) % 64) else wd y q) = wd y q % 2 ^ rr := by
    by_cases h : (L - 1) % 64 ≠ 0
    · rw [if_pos h, hmb]
      have : rr % 64 = rr := by omega
      rw [this]
    · rw [if_neg h]
      have : rr = 64 := by omega
      subst this
      rw [← B_def, Nat.mod_eq_of_lt (wd_lt y q)]
  have hkey : (wd y q % 2 ^ rr) * B ^ q + y % B ^ q = y % T := by
    rw [hTB, Nat.mod_mul]
    have : y / B ^ q % 2 ^ rr = wd y q % 2 ^ rr := by
      unfold wd; rw [Nat.mod_mod_of_dvd _ hdvd]
    rw [this]; grind
  unfold p2win
  simp only
  rw [← hq]
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 = min (nlen y - 1) q := ⟨_, rfl⟩
  rw [← hi0]
  obtain ⟨yi0, hyi0⟩ : ∃ yi0, yi0 = (if i0 = q then
      (if (L - 1) % 64 ≠ 0 then wd y i0 % 2 ^ ((L - 1) % 64) else wd y i0) else wd y i0) := ⟨_, rfl⟩
  rw [← hyi0]
  have hyi0B : yi0 < B := by
    rw [hyi0]; split
    · split
      · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (by
          rw [B_def]; exact Nat.pow_le_pow_right (by omega) (by omega))
      · exact wd_lt _ _
    · exact wd_lt _ _
  have hyT : y % T < T := Nat.mod_lt _ (by rw [hT]; exact Nat.two_pow_pos _)
  have he0 : (yi0 * B ^ i0 + y % B ^ i0) % T = y % T := by
    by_cases hc : i0 = q
    · have : yi0 = wd y q % 2 ^ rr := by
        rw [hyi0, if_pos hc, hc, hmask]
      rw [this, hc, hkey, Nat.mod_mod]
    · have hi : i0 = nlen y - 1 := by omega
      have : yi0 = wd y i0 := by rw [hyi0, if_neg hc]
      rw [this, ← mod_succ]
      have h1 := lt_B_nlen y
      rw [show i0 + 1 = nlen y by have := nlen_pos hy; omega, Nat.mod_eq_of_lt h1]
  have hsk := skipZero_spec y i0 yi0 hyi0B
  generalize skipZero y i0 yi0 = r at hsk ⊢
  have hL1 : 1 ≤ L := by omega
  have hTe : 2 ^ (L - 1) = T := hT.symm
  match r, hsk with
  | none, h =>
    simp only at h ⊢
    rw [h] at he0
    have := pow_mod_phi x L y 0 hx hL1 (by rw [hTe]; rw [← he0])
    rw [this]; simp; exact (Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))).symm
  | some (i, yi), h =>
    simp only at h ⊢
    obtain ⟨hne, hyiB, hee⟩ := h
    have hrun := winRun_rep w (PRep L x) _ hw0 hK hw64 (p2step_rep L x w hL1) (p2Pow L x)
      (fun d _ => p2Pow_rep L x hL1 d) y i yi (Nat.pos_of_ne_zero hne) hyiB
    rw [hee] at hrun
    rw [hrun.2]
    exact pow_mod_phi x L _ y hx hL1 (by rw [hTe]; exact he0)

/-! ### expNNPowerOfTwo (nat.go:906) -/

/-- `expNNPowerOfTwo`; `f` is a recursion budget (the Go function recurses at most once, on an odd base). -/
def expNNPowerOfTwo : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | f + 1, x, y, L =>
    if L = 1 then x % 2                                         -- return z.setWord(x[0] & 1)
    else if x % 2 = 0 then                                       -- x[0]&1 == 0
      if 1 < nlen y then 0                                       -- len(y) > 1
      else
        let i := tz x
        let prod := i * wd y 0                                    -- bits.Mul64(i, y[0])
        if prod / B ≠ 0 ∨ prod % B ≥ L then 0
        else
          let xOdd := x / 2 ^ i
          expNNPowerOfTwo f xOdd y (L - prod % B) * 2 ^ (prod % B)   -- z.lsh(z, adicity)
    else if L ≥ 48 ∧ bitLen y ≥ 48 then p2win 4 L x y else p2win 2 L x y

theorem tz_spec {x : Nat} (hx : 0 < x) : x = 2 ^ tz x * (x / 2 ^ tz x) ∧ (x / 2 ^ tz x) % 2 = 1 := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    unfold tz
    rw [dif_neg (by omega)]
    by_cases h : x % 2 = 1
    · simp [h]
    · simp only [h, if_false]
      have h2 : x % 2 = 0 := by omega
      have := ih (x / 2) (by omega) (by omega)
      obtain ⟨h1, h3⟩ := this
      rw [Nat.pow_add, Nat.pow_one]
      have e : x / (2 * 2 ^ tz (x / 2)) = x / 2 / 2 ^ tz (x / 2) := by
        rw [Nat.div_div_eq_div_mul]
      rw [e]
      refine ⟨?_, h3⟩
      have hx2 : x = 2 * (x / 2) := by omega
      grind

theorem pow_mod_one_odd (x y : Nat) (hy : 0 < y) : x ^ y % 2 = x % 2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h, Nat.zero_pow hy]
  · rw [h, Nat.one_pow]

theorem pow_even_mod_zero (x y L : Nat) (hx : x % 2 = 0) (hLy : L ≤ y) : x ^ y % 2 ^ L = 0 := by
  obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
  rw [Nat.mul_pow]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hLy) _)

/-- `expNNPowerOfTwo` on an odd base (any fuel ≥ 1). -/
theorem expNNPowerOfTwo_odd (f x y L : Nat) (hf : 1 ≤ f) (hx : x % 2 = 1) (hy : 0 < y) (hL : 1 ≤ L) :
    expNNPowerOfTwo f x y L = x ^ y % 2 ^ L := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  unfold expNNPowerOfTwo
  by_cases hL1 : L = 1
  · rw [if_pos hL1, hL1, pow_mod_one_odd x y hy]
  · rw [if_neg hL1, if_neg (by omega : ¬ x % 2 = 0)]
    have hL2 : 2 ≤ L := by omega
    split
    · exact p2win_correct 4 L x y (Or.inr rfl) hx hy hL2
    · exact p2win_correct 2 L x y (Or.inl rfl) hx hy hL2

/-- `expNNPowerOfTwo`, any positive base (fuel ≥ 2), for `2^L` with `L < 2^64`. -/
theorem expNNPowerOfTwo_correct (f x y L : Nat) (hf : 2 ≤ f) (hx : 0 < x) (hy : 0 < y) (hL : 1 ≤ L)
    (hLB : L < B) : expNNPowerOfTwo f x y L = x ^ y % 2 ^ L := by
  by_cases hxo : x % 2 = 1
  · exact expNNPowerOfTwo_odd f x y L (by omega) hxo hy hL
  have hxe : x % 2 = 0 := by omega
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  unfold expNNPowerOfTwo
  by_cases hL1 : L = 1
  · rw [if_pos hL1, hL1, pow_mod_one_odd x y hy]
  rw [if_neg hL1, if_pos hxe]
  by_cases hy1 : 1 < nlen y
  · rw [if_pos hy1]
    have : B ≤ y := by
      refine Nat.not_lt.mp (fun h => ?_)
      have := nlen_le_iff (x := y) (n := 1)
      rw [Nat.pow_one] at this
      have := this.mpr h; omega
    exact (pow_even_mod_zero x y L hxe (by omega)).symm
  · rw [if_neg hy1]
    have hyB : y < B := by
      have := nlen_le_iff (x := y) (n := 1)
      rw [Nat.pow_one] at this
      exact this.mp (by omega)
    have hw0 : wd y 0 = y := by unfold wd; simp [Nat.mod_eq_of_lt hyB]
    obtain ⟨hxs, hxodd⟩ := tz_spec hx
    simp only [hw0]
    obtain ⟨i, hi⟩ : ∃ i, i = tz x := ⟨_, rfl⟩
    rw [← hi] at hxs hxodd ⊢
    have hxe' : x = 2 ^ i * (x / 2 ^ i) := hxs
    have hi1 : 1 ≤ i := by
      refine Nat.one_le_iff_ne_zero.mpr (fun h0 => ?_)
      rw [h0] at hxodd hxe'; simp at hxodd hxe'; omega
    obtain ⟨xo, hxo⟩ : ∃ xo, xo = x / 2 ^ i := ⟨_, rfl⟩
    rw [← hxo] at hxe' hxodd ⊢
    have hpow : x ^ y = 2 ^ (i * y) * xo ^ y := by
      have : x ^ y = (2 ^ i * xo) ^ y := congrArg (· ^ y) hxe'
      rw [this, Nat.mul_pow, ← Nat.pow_mul]
    by_cases hge : L ≤ i * y
    · have hc : (i * y / B ≠ 0 ∨ i * y % B ≥ L) := by
        by_cases hlt : i * y < B
        · right; rw [Nat.mod_eq_of_lt hlt]; exact hge
        · left; intro h0; rw [Nat.div_eq_zero_iff] at h0
          omega
      rw [if_pos hc, hpow]
      exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hge) _)).symm
    · have hlt : i * y < B := by omega
      have hc : ¬ (i * y / B ≠ 0 ∨ i * y % B ≥ L) := by
        rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]; omega
      rw [if_neg hc, Nat.mod_eq_of_lt hlt]
      rw [expNNPowerOfTwo_odd f' xo y (L - i * y) (by omega) hxodd hy (by omega)]
      rw [hpow, Nat.mul_comm (2 ^ (i * y)) (xo ^ y)]
      have e : 2 ^ L = 2 ^ (L - i * y) * 2 ^ (i * y) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, Nat.mul_mod_mul_right]

end FvModexp.Exp
