import FvModexp.Proofs.Common.Slices
/-!
# basicMul, mulAddWW (natmul.go)

* `basicMul`    natmul.go:171   `basicMul(z, x, y)`: schoolbook, row by row with `addMulVVWW`
* `natMulAddWW` natmul.go:154   `(z nat) mulAddWW(x nat, y, r Word) nat`
-/
namespace FvModexp.Mdl

/-- The loop `for i, d := range y { if d != 0 { z[len(x)+i] = addMulVVWW(z[i:i+len(x)], z[i:i+len(x)], x, d, 0) } }`. -/
def basicMulLoop (x : List Nat) : Nat → List Nat → List Nat → List Nat
  | _, z, [] => z
  | i, z, d :: ys =>
    let z' := if d ≠ 0 then
        (let r := addMulVVWW (sl z i x.length) x d 0
         upd (upd z i r.1) (x.length + i) [r.2])
      else z
    basicMulLoop x (i + 1) z' ys

/-- natmul.go:171 `basicMul(z, x, y)`: returns the contents of `z[0:len(x)+len(y)]` (after `clear`, so independent of the old `z`). -/
def basicMul (x y : List Nat) : List Nat :=
  basicMulLoop x 0 (List.replicate (x.length + y.length) 0) y

theorem basicMulLoop_spec (x : List Nat) (hx : Wd x) : ∀ (ys : List Nat) (i : Nat) (z : List Nat),
    Wd ys → Wd z → z.length = x.length + i + ys.length → (∀ d ∈ z.drop (x.length + i), d = 0) →
    (basicMulLoop x i z ys).length = z.length ∧ Wd (basicMulLoop x i z ys) ∧
    val (basicMulLoop x i z ys) = val z + 2 ^ (64 * i) * (val x * val ys)
  | [], i, z, _, hz, _, _ => by simp [basicMulLoop, hz]
  | d :: ys, i, z, hys, hz, hlen, htail => by
    have hyd := Wd_cons.1 hys
    simp only [List.length_cons] at hlen
    unfold basicMulLoop
    simp only []
    have hdrop : ∀ d' ∈ z.drop (x.length + i + 1), d' = 0 := by
      intro d' hd'
      apply htail
      have : z.drop (x.length + i + 1) = (z.drop (x.length + i)).drop 1 := by simp [List.drop_drop]
      rw [this] at hd'
      exact List.mem_of_mem_drop hd'
    by_cases hd0 : d ≠ 0
    · rw [if_pos hd0]
      have hsl : (sl z i x.length).length = x.length := length_sl z i x.length (by omega)
      obtain ⟨a1, a2, a3, a4⟩ := addMulVVWW_spec (sl z i x.length) x d 0 (Wd_sl hz _ _) hx (by omega) hyd.1 (by decide)
      generalize hr : addMulVVWW (sl z i x.length) x d 0 = r at *
      obtain ⟨r1, r2⟩ := r
      simp only [] at a1 a2 a3 a4 ⊢
      rw [hsl] at a1 a4
      have hz1len : (upd z i r1).length = z.length := length_upd z r1 i (by omega)
      have hu1 := val_upd z r1 i (by omega)
      have hz1 : Wd (upd z i r1) := Wd_upd hz a2
      have hu2 := val_upd (upd z i r1) [r2] (x.length + i) (by rw [hz1len]; try simp only [List.length_singleton]; omega)
      have hz2 : Wd (upd (upd z i r1) (x.length + i) [r2]) := Wd_upd hz1 (Wd_cons.2 ⟨a3, Wd_nil⟩)
      have hz2len : (upd (upd z i r1) (x.length + i) [r2]).length = z.length := (length_upd _ _ _ (by rw [hz1len]; try simp only [List.length_singleton]; omega)).trans hz1len
      -- the old slice at x.length + i is zero
      have hdr : (upd z i r1).drop (x.length + i) = z.drop (x.length + i) :=
        drop_upd_far z r1 i (x.length + i) (by omega) (by omega)
      have hz0 : ((upd z i r1).drop (x.length + i)).take [r2].length = [0] := by
        rw [hdr]
        have hne : z.drop (x.length + i) ≠ [] := by
          intro e; have := congrArg List.length e; simp at this; omega
        obtain ⟨h0, t0, hh⟩ : ∃ h0 t0, z.drop (x.length + i) = h0 :: t0 := by
          cases h : z.drop (x.length + i) with
          | nil => exact absurd h hne
          | cons h0 t0 => exact ⟨h0, t0, rfl⟩
        have : h0 = 0 := htail h0 (by rw [hh]; simp)
        rw [hh, this]; simp
      rw [hz0] at hu2
      have htail2 : ∀ d' ∈ (upd (upd z i r1) (x.length + i) [r2]).drop (x.length + (i + 1)), d' = 0 := by
        intro d' hd'
        have : (upd (upd z i r1) (x.length + i) [r2]).drop (x.length + (i + 1)) = z.drop (x.length + i + 1) := by
          rw [drop_upd_far _ _ _ _ (by rw [hz1len]; try simp only [List.length_singleton]; omega) (by try simp only [List.length_singleton]; omega)]
          rw [drop_upd_far z r1 i _ (by omega) (by omega), Nat.add_assoc]
        rw [this] at hd'
        exact hdrop d' hd'
      obtain ⟨b1, b2, b3⟩ := basicMulLoop_spec x hx ys (i + 1) (upd (upd z i r1) (x.length + i) [r2]) hyd.2 hz2
        (by omega) htail2
      refine ⟨by rw [b1, hz2len], b2, ?_⟩
      rw [b3]
      simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero] at hu2 ⊢
      rw [pow_succ64]
      have e1 : 2 ^ (64 * i) * 2 ^ 64 = 2 ^ 64 * 2 ^ (64 * i) := Nat.mul_comm _ _
      have e2 : 2 ^ (64 * (x.length + i)) = 2 ^ (64 * x.length) * 2 ^ (64 * i) := by
        rw [Nat.mul_add, Nat.pow_add]
      -- val x * val (d :: ys) = val x * d + 2^64 * (val x * val ys)
      have hS : val (List.take r1.length (List.drop i z)) = val (sl z i x.length) := by rw [a1]; rfl
      rw [hS] at hu1
      have h5 := congrArg (fun t => 2 ^ (64 * i) * t) a4
      simp only [Nat.mul_add] at h5
      generalize val (sl z i x.length) = S at *
      generalize val (upd z i r1) = Z1 at *
      generalize val (upd (upd z i r1) (x.length + i) [r2]) = Z2 at *
      generalize val r1 = V at *
      generalize val z = Z at *
      generalize val x = X at *
      generalize val ys = Y at *
      generalize 2 ^ (64 * i) = P at *
      generalize 2 ^ (64 * x.length) = Q at *
      have e3 : P * (Q * r2) = P * Q * r2 := (Nat.mul_assoc _ _ _).symm
      rw [e2] at hu2
      have e4 : Q * P * r2 = P * Q * r2 := by rw [Nat.mul_comm Q P]
      have e5 : P * (X * d) = X * d * P := by grind
      have e6 : P * (X * (d + 2 ^ 64 * Y)) = P * (X * d) + 2 ^ 64 * P * (X * Y) := by grind
      omega
    · rw [if_neg hd0]
      have : d = 0 := by omega
      subst this
      obtain ⟨b1, b2, b3⟩ := basicMulLoop_spec x hx ys (i + 1) z hyd.2 hz (by omega) (by
        intro d' hd'; exact hdrop d' (by simpa [Nat.add_assoc] using hd'))
      refine ⟨b1, b2, ?_⟩
      rw [b3]
      simp only [val_cons, Nat.zero_add, pow_succ64]
      have : 2 ^ 64 * 2 ^ (64 * i) * (val x * val ys) = 2 ^ (64 * i) * (val x * (2 ^ 64 * val ys)) := by grind
      omega

theorem basicMul_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) :
    (basicMul x y).length = x.length + y.length ∧ Wd (basicMul x y) ∧ val (basicMul x y) = val x * val y := by
  unfold basicMul
  obtain ⟨h1, h2, h3⟩ := basicMulLoop_spec x hx y 0 (List.replicate (x.length + y.length) 0) hy (Wd_replicate_zero _)
    (by simp) (by
      intro d hd; have := List.eq_of_mem_replicate (List.mem_of_mem_drop hd); exact this)
  refine ⟨by rw [h1]; simp, h2, ?_⟩
  rw [h3, val_replicate_zero]; simp

/-- natmul.go:154 `(z nat) mulAddWW(x nat, y, r Word) nat`. -/
def natMulAddWW (x : List Nat) (y r : Nat) : List Nat :=
  if x.length = 0 ∨ y = 0 then natSetWord r else
  let t := mulAddVWW x y r          -- z[m] = mulAddVWW(z[0:m], x, y, r)
  norm (t.1 ++ [t.2])

theorem natMulAddWW_spec (x : List Nat) (y r : Nat) (hx : Wd x) (hy : y < 2 ^ 64) (hr : r < 2 ^ 64) :
    Wd (natMulAddWW x y r) ∧ val (natMulAddWW x y r) = val x * y + r ∧ Normed (natMulAddWW x y r) ∧
    (natMulAddWW x y r).length ≤ x.length + 1 := by
  unfold natMulAddWW
  by_cases h : x.length = 0 ∨ y = 0
  · rw [if_pos h]
    obtain ⟨a, b, c⟩ := natSetWord_spec r hr
    refine ⟨b, ?_, c, ?_⟩
    · rw [a]
      rcases h with h | h
      · have : x = [] := List.length_eq_zero_iff.1 h
        subst this; simp
      · subst h; simp
    · unfold natSetWord; split <;> simp
  · rw [if_neg h]
    obtain ⟨i1, i2, i3, i4⟩ := mulAddVWW_spec x y r hx hy hr
    refine ⟨Wd_norm (Wd_append.2 ⟨i2, by intro d hd; simp at hd; subst hd; exact i3⟩), ?_, normed_norm _, ?_⟩
    · rw [val_norm, val_append]
      simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero, i1]
      omega
    · refine Nat.le_trans (length_norm_le _) ?_
      rw [List.length_append, i1]; simp

/-! ## nat.mul structure (natmul.go:15-70), parametrised by the Karatsuba kernel and the recursive multiplier -/

/-- The loop `for i := n; i < m; i += n { t = t.mul(stk, x[i:min(i+n, len(x))], y); addTo(z[i:], t) }`. -/
def mulChunks (mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (n : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, z => z
  | f + 1, i, z =>
    if i < x.length then
      let t := mulRec ((x.drop i).take n) y
      mulChunks mulRec x y n f (i + n) (z.take i ++ addTo (z.drop i) t)
    else z

theorem mulChunks_spec (mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (n : Nat) (hx : Wd x) (hy : Wd y)
    (hn : 1 ≤ n) (hyn : y.length = n)
    (hrec : ∀ a b, Wd a → Wd b → Wd (mulRec a b) ∧ val (mulRec a b) = val a * val b ∧ (mulRec a b).length ≤ a.length + b.length) :
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
      obtain ⟨t1, t2, t3⟩ := hrec ((x.drop i).take n) y ((hx.drop i).take n) hy
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
      obtain ⟨b1, b2, b3⟩ := mulChunks_spec mulRec x y n hx hy hn hyn hrec f (i + n)
        (z.take i ++ addTo (z.drop i) (mulRec ((x.drop i).take n) y)) hz' hl' (by
          have : (f + 1) * n = f * n + n := Nat.succ_mul f n
          omega) hv'
      exact ⟨by rw [b1, hl', hlen], b2, b3⟩
    · rw [if_neg hi]
      have : x.take i = x := List.take_of_length_le (by omega)
      rw [this] at hv
      exact ⟨rfl, hz, by rw [hv]⟩

/-- karatsubaThreshold (natmul.go:12). -/
def karatsubaThreshold : Nat := 40

/-- `(z nat) mul(stk, x, y)` for `len(x) >= len(y)` (natmul.go:15-69), with the Karatsuba kernel `kar` (`karatsuba(stk, z[:2n], x[:n], y)`)
and the recursive multiplier `mulRec` (`t.mul(stk, ...)`) as parameters. -/
def natMulM (kar mulRec : List Nat → List Nat → List Nat) (x y : List Nat) : List Nat :=
  let m := x.length
  let n := y.length
  if m = 0 ∨ n = 0 then [] else
  if n = 1 then natMulAddWW x (y.getD 0 0) 0 else
  if n < karatsubaThreshold then norm (basicMul x y) else
  let z1 := kar (x.take n) y
  norm (if n < m then mulChunks mulRec x y n m n (z1 ++ List.replicate (m - n) 0) else z1)

/-- nat.go `(z nat) mul`: the `m < n` case swaps the operands (`return z.mul(stk, y, x)`). -/
def natMulS (kar mulRec : List Nat → List Nat → List Nat) (x y : List Nat) : List Nat :=
  if x.length < y.length then natMulM kar mulRec y x else natMulM kar mulRec x y

theorem natMulM_spec (kar mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (hx : Wd x) (hy : Wd y)
    (hl : y.length ≤ x.length)
    (hkar : ∀ a b, Wd a → Wd b → a.length = b.length → karatsubaThreshold ≤ b.length →
      (kar a b).length = 2 * b.length ∧ Wd (kar a b) ∧ val (kar a b) = val a * val b)
    (hrec : ∀ a b, Wd a → Wd b → Wd (mulRec a b) ∧ val (mulRec a b) = val a * val b ∧ (mulRec a b).length ≤ a.length + b.length) :
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
  obtain ⟨k1, k2, k3⟩ := hkar (x.take y.length) y (hx.take _) hy hxn hth
  by_cases h3 : y.length < x.length
  · rw [if_pos h3]
    have hz0 : Wd (kar (x.take y.length) y ++ List.replicate (x.length - y.length) 0) :=
      Wd_append.2 ⟨k2, Wd_replicate_zero _⟩
    have hzl : (kar (x.take y.length) y ++ List.replicate (x.length - y.length) 0).length = x.length + y.length := by
      rw [List.length_append, k1, List.length_replicate]; omega
    obtain ⟨b1, b2, b3⟩ := mulChunks_spec mulRec x y y.length hx hy (by omega) rfl hrec x.length y.length
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

theorem natMulS_spec (kar mulRec : List Nat → List Nat → List Nat) (x y : List Nat) (hx : Wd x) (hy : Wd y)
    (hkar : ∀ a b, Wd a → Wd b → a.length = b.length → karatsubaThreshold ≤ b.length →
      (kar a b).length = 2 * b.length ∧ Wd (kar a b) ∧ val (kar a b) = val a * val b)
    (hrec : ∀ a b, Wd a → Wd b → Wd (mulRec a b) ∧ val (mulRec a b) = val a * val b ∧ (mulRec a b).length ≤ a.length + b.length) :
    Wd (natMulS kar mulRec x y) ∧ val (natMulS kar mulRec x y) = val x * val y ∧ Normed (natMulS kar mulRec x y) ∧
    (natMulS kar mulRec x y).length ≤ x.length + y.length := by
  unfold natMulS
  by_cases h : x.length < y.length
  · rw [if_pos h]
    obtain ⟨a, b, c, d⟩ := natMulM_spec kar mulRec y x hy hx (by omega) hkar hrec
    exact ⟨a, by rw [b, Nat.mul_comm], c, by omega⟩
  · rw [if_neg h]
    exact natMulM_spec kar mulRec x y hx hy (by omega) hkar hrec

end FvModexp.Mdl
