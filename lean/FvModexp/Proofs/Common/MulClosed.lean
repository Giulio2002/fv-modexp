import FvModexp.Proofs.Common.KaratsubaSqr
/-!
# Closed recursive multiplication / squaring: `natMul`, `natSqr` (natmul.go:16, 73)

`nat.mul` -> `karatsuba` -> `nat.mul` ... is a recursion through a higher-order parameter, so the closed models are fuel-indexed:
`natMulF f` / `natSqrF f` are the parametrised models (`natMulS`, `karatsuba`, `natSqrP`, `karatsubaSqr`) with the recursive callee
`natMulF (f-1)` / `natSqrF (f-1)`; fuel `0` returns `[]` (unreachable: `natMulF_spec` proves that `mu x y < f` fuel suffices, with
`mu` the lexicographic measure (2 * min length, unequal)).  `natMul` / `natSqr` pick a sufficient fuel.

NatMul1's `natMulM_spec` / `mulChunks_spec` ask for the contract of the recursive callee on *all* inputs; the recursion only provides it
on smaller inputs, hence the pointwise-restricted copies `mulChunks_spec'`, `natMulM_spec'`, `natMulS_spec'` below (same proofs).
-/
namespace FvModexp.Mdl

theorem mulChunks_spec' (mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (n : Nat) (hx : Wd x) (hy : Wd y)
    (hn : 1 ≤ n) (hyn : y.length = n)
    (hrec : ∀ a, Wd a → a.length ≤ n →
      Wd (mulRec a y) ∧ val (mulRec a y) = val a * val y ∧ (mulRec a y).length ≤ a.length + y.length) :
    ∀ (fuel i : Nat) (z : List Nat), Wd z → z.length = x.length + n → x.length ≤ i + fuel * n →
      val z = val y * val (x.take i) →
      (mulChunks mulRec x y n fuel i z).length = z.length ∧ Wd (mulChunks mulRec x y n fuel i z) ∧
      val (mulChunks mulRec x y n fuel i z) = val y * val x
  | 0, i, z, hz, hlen, hf, hv => by
    unfold mulChunks
    have : x.take i = x := List.take_of_length_le (by omega)
    rw [this] at hv
    exact ⟨rfl, hz, by rw [hv]⟩
  | f + 1, i, z, hz, hlen, hf, hv => by
    unfold mulChunks
    by_cases hi : i < x.length
    · rw [if_pos hi]
      simp only []
      obtain ⟨t1, t2, t3⟩ := hrec ((x.drop i).take n) ((hx.drop i).take n) (by simp [List.length_take]; omega)
      have hcl : ((x.drop i).take n).length ≤ x.length - i := by rw [List.length_take, List.length_drop]; omega
      have hzi : i ≤ z.length := by omega
      have hzs := val_split z i hzi
      have hzd : Wd (z.drop i) := hz.drop i
      have hzdl : (z.drop i).length = x.length + n - i := by simp; omega
      have hzt : (z.take i).length = i := by simp [List.length_take]; omega
      have hxt : x.take (i + n) = x.take i ++ (x.drop i).take n := List.take_add
      have hxtl : (x.take i).length = i := by simp [List.length_take]; omega
      have hvt : val (x.take (i + n)) = val (x.take i) + 2 ^ (64 * i) * val ((x.drop i).take n) := by
        rw [hxt, val_append, hxtl]
      have hvlt : val y * val (x.take (i + n)) < 2 ^ (64 * (x.length + n)) := by
        have hlt1 := val_lt hy
        rw [hyn] at hlt1
        have hlt2 : val (x.take (i + n)) < 2 ^ (64 * (x.take (i + n)).length) := val_lt (hx.take _)
        have hlen2 : (x.take (i + n)).length ≤ x.length := by rw [List.length_take]; omega
        have : 2 ^ (64 * (x.take (i + n)).length) ≤ 2 ^ (64 * x.length) := Nat.pow_le_pow_right (by decide) (by omega)
        have h3 : val y * val (x.take (i + n)) < 2 ^ (64 * n) * 2 ^ (64 * x.length) :=
          Nat.mul_lt_mul'' hlt1 (by omega)
        have e : 2 ^ (64 * n) * 2 ^ (64 * x.length) = 2 ^ (64 * (x.length + n)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [e] at h3
        exact h3
      -- val z + B^i * val t = val y * val (x.take (i+n))
      have hsum : val z + 2 ^ (64 * i) * val (mulRec ((x.drop i).take n) y) = val y * val (x.take (i + n)) := by
        rw [t2, hv, hvt]
        generalize val y = Y
        generalize val (x.take i) = A
        generalize val ((x.drop i).take n) = C
        generalize 2 ^ (64 * i) = P
        grind
      have hno : val (z.drop i) + val (mulRec ((x.drop i).take n) y) < 2 ^ (64 * (z.drop i).length) := by
        have hP : 0 < 2 ^ (64 * i) := Nat.two_pow_pos _
        refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * i)) ?_
        have e : 2 ^ (64 * i) * 2 ^ (64 * (z.drop i).length) = 2 ^ (64 * (x.length + n)) := by
          rw [← Nat.pow_add, ← Nat.mul_add]; congr 2; omega
        rw [e, Nat.mul_add]
        omega
      obtain ⟨a1, a2, a3⟩ := addTo_spec (z.drop i) (mulRec ((x.drop i).take n) y) hzd t1 (by omega) hno
      have hz' : Wd (z.take i ++ addTo (z.drop i) (mulRec ((x.drop i).take n) y)) := Wd_append.2 ⟨hz.take _, a2⟩
      have hl' : (z.take i ++ addTo (z.drop i) (mulRec ((x.drop i).take n) y)).length = x.length + n := by
        rw [List.length_append, a1, hzt, hzdl]; omega
      have hv' : val (z.take i ++ addTo (z.drop i) (mulRec ((x.drop i).take n) y)) = val y * val (x.take (i + n)) := by
        rw [val_append, hzt, a3, ← hsum]
        have := Nat.mul_add (2 ^ (64 * i)) (val (z.drop i)) (val (mulRec ((x.drop i).take n) y))
        omega
      obtain ⟨b1, b2, b3⟩ := mulChunks_spec' mulRec x y n hx hy hn hyn hrec f (i + n)
        (z.take i ++ addTo (z.drop i) (mulRec ((x.drop i).take n) y)) hz' hl' (by
          have : (f + 1) * n = f * n + n := Nat.succ_mul f n
          omega) hv'
      exact ⟨by rw [b1, hl', hlen], b2, b3⟩
    · rw [if_neg hi]
      have : x.take i = x := List.take_of_length_le (by omega)
      rw [this] at hv
      exact ⟨rfl, hz, by rw [hv]⟩


theorem natMulM_spec' (kar mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (hx : Wd x) (hy : Wd y)
    (hl : y.length ≤ x.length)
    (hkar : karatsubaThreshold ≤ y.length →
      (kar (x.take y.length) y).length = 2 * y.length ∧ Wd (kar (x.take y.length) y) ∧
        val (kar (x.take y.length) y) = val (x.take y.length) * val y)
    (hrec : y.length < x.length → ∀ a, Wd a → a.length ≤ y.length →
      Wd (mulRec a y) ∧ val (mulRec a y) = val a * val y ∧ (mulRec a y).length ≤ a.length + y.length) :
    Wd (natMulM kar mulRec x y) ∧ val (natMulM kar mulRec x y) = val x * val y ∧ Normed (natMulM kar mulRec x y) ∧
    (natMulM kar mulRec x y).length ≤ x.length + y.length := by
  unfold natMulM
  simp only []
  by_cases h0 : x.length = 0 ∨ y.length = 0
  · rw [if_pos h0]
    refine ⟨Wd_nil, ?_, rfl, by simp⟩
    rcases h0 with h0 | h0
    · have : x = [] := List.length_eq_zero_iff.1 h0
      subst this; simp
    · have : y = [] := List.length_eq_zero_iff.1 h0
      subst this; simp
  rw [if_neg h0]
  by_cases h1 : y.length = 1
  · rw [if_pos h1]
    obtain ⟨a, b, c, d⟩ := natMulAddWW_spec x (y.getD 0 0) 0 hx (by
      cases y with
      | nil => simp at h1
      | cons d ds => exact (Wd_cons.1 hy).1) (by decide)
    refine ⟨a, ?_, c, by omega⟩
    rw [b]
    cases y with
    | nil => simp at h1
    | cons d ds =>
      have : ds = [] := List.length_eq_zero_iff.1 (by simpa using h1)
      subst this
      simp
  rw [if_neg h1]
  by_cases h2 : y.length < karatsubaThreshold
  · rw [if_pos h2]
    obtain ⟨a, b, c⟩ := basicMul_spec x y hx hy
    refine ⟨Wd_norm b, by rw [val_norm, c], normed_norm _, ?_⟩
    exact Nat.le_trans (length_norm_le _) (by omega)
  rw [if_neg h2]
  have hth : karatsubaThreshold ≤ y.length := by omega
  have hxn : (x.take y.length).length = y.length := by simp [List.length_take]; omega
  obtain ⟨k1, k2, k3⟩ := hkar hth
  by_cases h3 : y.length < x.length
  · rw [if_pos h3]
    have hz0 : Wd (kar (x.take y.length) y ++ List.replicate (x.length - y.length) 0) :=
      Wd_append.2 ⟨k2, Wd_replicate_zero _⟩
    have hzl : (kar (x.take y.length) y ++ List.replicate (x.length - y.length) 0).length = x.length + y.length := by
      rw [List.length_append, k1, List.length_replicate]; omega
    obtain ⟨b1, b2, b3⟩ := mulChunks_spec' mulRec x y y.length hx hy (by omega) rfl (hrec h3) x.length y.length
      (kar (x.take y.length) y ++ List.replicate (x.length - y.length) 0) hz0 hzl (by
        have : x.length ≤ x.length * y.length := Nat.le_mul_of_pos_right _ (by omega)
        omega) (by
        rw [val_append_zeros, k3, Nat.mul_comm])
    refine ⟨Wd_norm b2, by rw [val_norm, b3, Nat.mul_comm], normed_norm _, ?_⟩
    exact Nat.le_trans (length_norm_le _) (by omega)
  · rw [if_neg h3]
    have hxy : x.length = y.length := by omega
    have hxt : x.take y.length = x := by rw [← hxy]; exact List.take_length
    rw [hxt] at k1 k2 k3
    rw [hxt]
    refine ⟨Wd_norm k2, by rw [val_norm, k3], normed_norm _, ?_⟩
    exact Nat.le_trans (length_norm_le _) (by rw [k1]; omega)


theorem natMulS_spec' (kar mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (hx : Wd x) (hy : Wd y)
    (hkar1 : y.length ≤ x.length → karatsubaThreshold ≤ y.length →
      (kar (x.take y.length) y).length = 2 * y.length ∧ Wd (kar (x.take y.length) y) ∧
        val (kar (x.take y.length) y) = val (x.take y.length) * val y)
    (hkar2 : x.length < y.length → karatsubaThreshold ≤ x.length →
      (kar (y.take x.length) x).length = 2 * x.length ∧ Wd (kar (y.take x.length) x) ∧
        val (kar (y.take x.length) x) = val (y.take x.length) * val x)
    (hrec1 : y.length < x.length → ∀ a, Wd a → a.length ≤ y.length →
      Wd (mulRec a y) ∧ val (mulRec a y) = val a * val y ∧ (mulRec a y).length ≤ a.length + y.length)
    (hrec2 : x.length < y.length → ∀ a, Wd a → a.length ≤ x.length →
      Wd (mulRec a x) ∧ val (mulRec a x) = val a * val x ∧ (mulRec a x).length ≤ a.length + x.length) :
    Wd (natMulS kar mulRec x y) ∧ val (natMulS kar mulRec x y) = val x * val y ∧ Normed (natMulS kar mulRec x y) ∧
    (natMulS kar mulRec x y).length ≤ x.length + y.length := by
  unfold natMulS
  by_cases h : x.length < y.length
  · rw [if_pos h]
    obtain ⟨a, b, c, d⟩ := natMulM_spec' kar mulRec y x hy hx (by omega) (hkar2 h) hrec2
    exact ⟨a, by rw [b, Nat.mul_comm], c, by omega⟩
  · rw [if_neg h]
    exact natMulM_spec' kar mulRec x y hx hy (by omega) (hkar1 (by omega)) (hrec1)

/-! ## the closed models -/

/-- Fuel-indexed `nat.mul` (natmul.go:16): `kar` is `karatsuba(stk, z[:2n], x[:n], y)` with its multiplier `natMulF f`. -/
def natMulF : Nat → List Nat → List Nat → List Nat
  | 0, _, _ => []
  | f + 1, x, y => natMulS (fun a b => karatsuba (natMulF f) a b) (natMulF f) x y

/-- Fuel-indexed `nat.sqr` (natmul.go:73). -/
def natSqrF : Nat → List Nat → List Nat
  | 0, _ => []
  | f + 1, x => natSqrP (karatsubaSqr (natSqrF f)) x

/-- The recursion measure of `nat.mul x y` (`mul`'s `m < n` swap does not change it; the chunk loop strictly decreases it). -/
def mulMu (x y : List Nat) : Nat :=
  2 * min x.length y.length + min 1 (max x.length y.length - min x.length y.length)

/-- natmul.go:16 `(z nat) mul(stk, x, y)`. -/
def natMul (x y : List Nat) : List Nat := natMulF (2 * (x.length + y.length) + 2) x y

/-- natmul.go:73 `(z nat) sqr(stk, x)`. -/
def natSqr (x : List Nat) : List Nat := natSqrF (x.length + 1) x

theorem natMulF_spec : ∀ (f : Nat) (x y : List Nat), Wd x → Wd y → mulMu x y < f →
    Wd (natMulF f x y) ∧ val (natMulF f x y) = val x * val y ∧ Normed (natMulF f x y) ∧
    (natMulF f x y).length ≤ x.length + y.length
  | 0, x, y, _, _, h => by omega
  | f + 1, x, y, hx, hy, hf => by
    unfold natMulF
    have IH := natMulF_spec f
    unfold mulMu at hf
    refine natMulS_spec' _ _ x y hx hy (fun hyx h40 => ?_) (fun hxy h40 => ?_) (fun hyx a ha hal => ?_) (fun hxy a ha hal => ?_)
    · exact karatsuba_spec (natMulF f) (x.take y.length) y
        (fun a b ha hb la lb => IH a b ha hb (by unfold mulMu; omega)) (hx.take _) hy (by simp [List.length_take]; omega)
    · exact karatsuba_spec (natMulF f) (y.take x.length) x
        (fun a b ha hb la lb => IH a b ha hb (by unfold mulMu; omega)) (hy.take _) hx (by simp [List.length_take]; omega)
    · have r := IH a y ha hy (by unfold mulMu; omega)
      exact ⟨r.1, r.2.1, r.2.2.2⟩
    · have r := IH a x ha hx (by unfold mulMu; omega)
      exact ⟨r.1, r.2.1, r.2.2.2⟩

theorem natMul_spec : MulContract natMul := by
  intro a b ha hb
  have := natMulF_spec (2 * (a.length + b.length) + 2) a b ha hb (by unfold mulMu; omega)
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩

theorem natSqrF_spec : ∀ (f : Nat) (x : List Nat), Wd x → x.length < f →
    Wd (natSqrF f x) ∧ val (natSqrF f x) = val x * val x ∧ Normed (natSqrF f x) ∧ (natSqrF f x).length ≤ 2 * x.length
  | 0, x, _, h => by omega
  | f + 1, x, hx, hf => by
    unfold natSqrF
    have IH := natSqrF_spec f
    exact natSqrP_at _ x hx (fun h80 =>
      karatsubaSqr_spec (natSqrF f) x (fun a ha la => IH a ha (by omega)) hx)

theorem natSqr_spec : SqrContract natSqr := by
  intro a ha
  exact natSqrF_spec (a.length + 1) a ha (by omega)

/-! ## closed Karatsuba kernels -/

/-- `karatsuba(stk, z, x, y)` with the closed multiplier. -/
def karatsubaC (x y : List Nat) : List Nat := karatsuba natMul x y

theorem karatsubaC_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) (hl : x.length = y.length) :
    (karatsubaC x y).length = 2 * y.length ∧ Wd (karatsubaC x y) ∧ val (karatsubaC x y) = val x * val y :=
  karatsuba_spec natMul x y (fun a b ha hb _ _ => natMul_spec a b ha hb) hx hy hl

/-- `karatsubaSqr(stk, z, x)` with the closed squarer. -/
def karatsubaSqrC (x : List Nat) : List Nat := karatsubaSqr natSqr x

theorem karatsubaSqrC_spec (x : List Nat) (hx : Wd x) :
    (karatsubaSqrC x).length = 2 * x.length ∧ Wd (karatsubaSqrC x) ∧ val (karatsubaSqrC x) = val x * val x :=
  karatsubaSqr_spec natSqr x (fun a ha _ => natSqr_spec a ha) hx

theorem norm_unique : ∀ (a b : List Nat), Wd a → Wd b → Normed a → Normed b → val a = val b → a = b
  | [], [], _, _, _, _, _ => rfl
  | [], e :: es, _, hb, _, nb, h => by
    have := normed_val_pos hb nb (by simp); rw [val_nil] at h; omega
  | d :: ds, [], ha, _, na, _, h => by
    have := normed_val_pos ha na (by simp); rw [val_nil] at h; omega
  | d :: ds, e :: es, ha, hb, na, nb, h => by
    have hd := Wd_cons.1 ha
    have he := Wd_cons.1 hb
    simp only [val_cons] at h
    have h1 : d = e := by omega
    subst h1
    have h2 : val ds = val es := by omega
    rw [norm_unique ds es hd.2 he.2 (normed_cons.1 na).1 (normed_cons.1 nb).1 h2]

/-- `nat.mul` agrees with the fuel-indexed model for any fuel above the measure (so the choice of fuel is immaterial). -/
theorem natMulF_stable (f g : Nat) (x y : List Nat) (hx : Wd x) (hy : Wd y) (hf : mulMu x y < f) (hg : mulMu x y < g) :
    natMulF f x y = natMulF g x y := by
  obtain ⟨a1, a2, a3, _⟩ := natMulF_spec f x y hx hy hf
  obtain ⟨b1, b2, b3, _⟩ := natMulF_spec g x y hx hy hg
  exact norm_unique _ _ a1 b1 a3 b3 (a2.trans b2.symm)

end FvModexp.Mdl
