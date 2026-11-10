import FvModexp.Proofs.Common.NatMul1
import FvModexp.Proofs.Common.IntOps
/-!
# basicSqr, nat.sqr (natmul.go:73-133)

* `addMulStep`   the statement `z[len(x)+i] = addMulVVWW(z[i:i+len(x)], z[i:i+len(x)], x, d, 0)` (natmul.go:155, 129)
* `basicSqr`     natmul.go:113 `basicSqr(stk, z, x)` (returns `z[0:2n]`)
* `natSqrP`       natmul.go:73 `(z nat) sqr(stk, x)`, parametrised by the `karatsubaSqr` kernel `ksqr`
-/
namespace FvModexp.Mdl

theorem zero_drop_mono {z : List Nat} {a b : Nat} (h : ∀ e ∈ z.drop a, e = 0) (hab : a ≤ b) :
    ∀ e ∈ z.drop b, e = 0 := by
  intro e he
  have : z.drop b = (z.drop a).drop (b - a) := by rw [List.drop_drop]; congr 1; omega
  rw [this] at he; exact h e (List.mem_of_mem_drop he)

theorem zero_sl {z : List Nat} {a i n : Nat} (h : ∀ e ∈ z.drop a, e = 0) (hai : a ≤ i) :
    ∀ e ∈ sl z i n, e = 0 :=
  fun e he => zero_drop_mono h hai e (List.mem_of_mem_take he)

theorem val_upd_zero (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length)
    (hz : ∀ e ∈ sl z i l.length, e = 0) :
    val (upd z i l) = val z + 2 ^ (64 * i) * val l := by
  have h1 := val_upd z l i h
  have h2 : val ((z.drop i).take l.length) = 0 := val_eq_zero_iff.2 hz
  rw [h2] at h1; omega

theorem take_upd_le (z l : List Nat) (i j : Nat) (hij : i ≤ j) (h : j + l.length ≤ z.length) :
    (upd z j l).take i = z.take i := by
  have h1 : (upd z j l).take i = ((upd z j l).take j).take i := by
    rw [List.take_take]; congr 1; omega
  rw [h1, take_upd_near z l j h, List.take_take]; congr 1; omega

/-! ## the fused multiply-accumulate statement -/

/-- `z[len(x)+i] = addMulVVWW(z[i:i+len(x)], z[i:i+len(x)], x, d, 0)`. -/
def addMulStep (z x : List Nat) (i d : Nat) : List Nat :=
  let r := addMulVVWW (sl z i x.length) x d 0
  upd (upd z i r.1) (x.length + i) [r.2]

theorem addMulStep_spec (z x : List Nat) (i d : Nat) (hz : Wd z) (hx : Wd x) (hd : d < 2 ^ 64)
    (hlen : x.length + i < z.length) (hslot : ∀ e ∈ z.drop (x.length + i), e = 0) :
    (addMulStep z x i d).length = z.length ∧ Wd (addMulStep z x i d) ∧
    val (addMulStep z x i d) = val z + 2 ^ (64 * i) * (val x * d) ∧
    (addMulStep z x i d).drop (x.length + i + 1) = z.drop (x.length + i + 1) ∧
    (addMulStep z x i d).take i = z.take i := by
  unfold addMulStep
  have hsl : (sl z i x.length).length = x.length := length_sl z i x.length (by omega)
  obtain ⟨a1, a2, a3, a4⟩ := addMulVVWW_spec (sl z i x.length) x d 0 (Wd_sl hz _ _) hx (by omega) hd (by decide)
  generalize hr : addMulVVWW (sl z i x.length) x d 0 = r at *
  obtain ⟨r1, r2⟩ := r
  simp only [] at a1 a2 a3 a4 ⊢
  rw [hsl] at a1 a4
  have hz1len : (upd z i r1).length = z.length := length_upd z r1 i (by omega)
  have hu1 := val_upd z r1 i (by omega)
  have hz1 : Wd (upd z i r1) := Wd_upd hz a2
  have hr2 : Wd [r2] := Wd_cons.2 ⟨a3, Wd_nil⟩
  have hu2 := val_upd (upd z i r1) [r2] (x.length + i) (by rw [hz1len]; simp only [List.length_singleton]; omega)
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
    have : h0 = 0 := hslot h0 (by rw [hh]; simp)
    rw [hh, this]; simp
  rw [hz0] at hu2
  have hz2len : (upd (upd z i r1) (x.length + i) [r2]).length = z.length :=
    (length_upd _ _ _ (by rw [hz1len]; simp only [List.length_singleton]; omega)).trans hz1len
  refine ⟨hz2len, Wd_upd hz1 hr2, ?_, ?_, ?_⟩
  · simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero] at hu2 ⊢
    have hS : val (List.take r1.length (List.drop i z)) = val (sl z i x.length) := by rw [a1]; rfl
    rw [hS] at hu1
    have h5 := congrArg (fun t => 2 ^ (64 * i) * t) a4
    simp only [Nat.mul_add] at h5
    have e2 : 2 ^ (64 * (x.length + i)) = 2 ^ (64 * x.length) * 2 ^ (64 * i) := by
      rw [Nat.mul_add, Nat.pow_add]
    rw [e2] at hu2
    generalize val (sl z i x.length) = S at *
    generalize val (upd z i r1) = Z1 at *
    generalize val (upd (upd z i r1) (x.length + i) [r2]) = Z2 at *
    generalize val r1 = V at *
    generalize val z = Z at *
    generalize val x = X at *
    generalize 2 ^ (64 * i) = P at *
    generalize 2 ^ (64 * x.length) = Q at *
    have e3 : P * (Q * r2) = Q * P * r2 := by grind
    have e5 : P * (X * d) = P * (X * d) := rfl
    omega
  · rw [drop_upd_far _ _ _ _ (by rw [hz1len]; simp only [List.length_singleton]; omega) (by simp only [List.length_singleton]; omega)]
    rw [drop_upd_far z r1 i _ (by omega) (by omega)]
  · rw [take_upd_le _ _ _ _ (by omega) (by rw [hz1len]; simp only [List.length_singleton]; omega), take_upd_near z r1 i (by omega)]

/-! ## basicSqr -/

theorem take_upd_exact (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) :
    (upd z i l).take (i + l.length) = z.take i ++ l := by
  unfold upd
  have h1 : (z.take i).length = i := by simp [List.length_take]; omega
  have h2 : (z.take i ++ l).length = i + l.length := by simp [h1]
  have := List.take_left' (l₂ := z.drop (i + l.length)) h2
  exact this

theorem val_take_succ (x : List Nat) (k : Nat) (hk : k < x.length) :
    val (x.take (k + 1)) = val (x.take k) + 2 ^ (64 * k) * x.getD k 0 := by
  have h1 : x.take (k + 1) = x.take k ++ [x.getD k 0] := by
    rw [List.take_succ]
    have : x[k]? = some (x.getD k 0) := by
      rw [List.getD_eq_getElem?_getD]; simp [List.getElem?_eq_getElem hk]
    rw [this]; rfl
  have h2 : (x.take k).length = k := by simp [List.length_take]; omega
  rw [h1, val_append, h2]; simp

/-- The loop `for i := 1; i < n; i++ { ... }` of natmul.go:124-130; `f` is fuel, `(z, t)` the state. -/
def basicSqrLoop (x : List Nat) : Nat → Nat → List Nat → List Nat → List Nat × List Nat
  | 0, _, z, t => (z, t)
  | f + 1, i, z, t =>
    if i < x.length then
      let d := x.getD i 0
      let p := mulWW d d                         -- z[2*i+1], z[2*i] = mulWW(d, d)
      let z' := upd z (2 * i) [p.2, p.1]
      let t' := addMulStep t (x.take i) i d      -- t[2*i] = addMulVVWW(t[i:2*i], t[i:2*i], x[0:i], d, 0)
      basicSqrLoop x f (i + 1) z' t'
    else (z, t)

/-- natmul.go:113 `basicSqr(stk, z, x)`; `z` is the incoming (arbitrary) content of `z[0:2n]`; returns the final `z[0:2n]`. -/
def basicSqr (z x : List Nat) : List Nat :=
  let n := x.length
  if n < 12 then basicMul x x else
  let t0 := List.replicate (2 * n) 0                          -- t := stk.nat(2n); clear(t)
  let q := mulWW (x.getD 0 0) (x.getD 0 0)
  let z0 := upd z 0 [q.2, q.1]                                -- z[1], z[0] = mulWW(x[0], x[0])
  let r := basicSqrLoop x (n - 1) 1 z0 t0
  let l := lshVU (sl r.2 1 (2 * n - 2)) 1                      -- t[2n-1] = lshVU(t[1:2n-1], t[1:2n-1], 1)
  let t2 := upd (upd r.2 1 l.1) (2 * n - 1) [l.2]
  (addVV r.1 t2).1                                            -- addVV(z, z, t)

theorem basicSqrLoop_spec (x : List Nat) (hx : Wd x) (zi : List Nat) :
    ∀ (f k : Nat) (z t : List Nat), Wd z → Wd t → z.length = 2 * x.length → t.length = 2 * x.length →
      1 ≤ k → k + f = x.length →
      z.drop (2 * k) = zi.drop (2 * k) →
      (∀ e ∈ t.drop (2 * k - 1), e = 0) → (∀ e ∈ t.take 1, e = 0) →
      val (z.take (2 * k)) + 2 * val t = val (x.take k) ^ 2 →
      (basicSqrLoop x f k z t).1.length = 2 * x.length ∧ Wd (basicSqrLoop x f k z t).1 ∧
      (basicSqrLoop x f k z t).2.length = 2 * x.length ∧ Wd (basicSqrLoop x f k z t).2 ∧
      (∀ e ∈ (basicSqrLoop x f k z t).2.drop (2 * x.length - 1), e = 0) ∧
      (∀ e ∈ (basicSqrLoop x f k z t).2.take 1, e = 0) ∧
      val ((basicSqrLoop x f k z t).1.take (2 * x.length)) + 2 * val (basicSqrLoop x f k z t).2 = val x ^ 2
  | 0, k, z, t, hz, ht, hzl, htl, hk, hkf, hzd, htd, ht1, hv => by
    have : k = x.length := by omega
    subst this
    unfold basicSqrLoop
    refine ⟨hzl, hz, htl, ht, htd, ht1, ?_⟩
    rw [hv, List.take_of_length_le (by omega)]
  | f + 1, k, z, t, hz, ht, hzl, htl, hk, hkf, hzd, htd, ht1, hv => by
    have hkn : k < x.length := by omega
    unfold basicSqrLoop
    rw [if_pos hkn]
    simp only []
    have hxk : (x.take k).length = k := by simp [List.length_take]; omega
    have hd : x.getD k 0 < 2 ^ 64 := by
      have : x.getD k 0 ∈ x := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkn]; simp
      exact hx _ this
    have hxw : Wd (x.take k) := hx.take k
    -- t step
    have hts := addMulStep_spec t (x.take k) k (x.getD k 0) ht hxw hd (by rw [hxk]; omega) (by
      rw [hxk]; exact zero_drop_mono htd (by omega))
    rw [hxk] at hts
    obtain ⟨s1, s2, s3, s4, s5⟩ := hts
    -- z step
    obtain ⟨m1, m2, m3⟩ : (mulWW (x.getD k 0) (x.getD k 0)).1 * 2 ^ 64 + (mulWW (x.getD k 0) (x.getD k 0)).2 = x.getD k 0 * x.getD k 0 ∧
        (mulWW (x.getD k 0) (x.getD k 0)).1 < 2 ^ 64 ∧ (mulWW (x.getD k 0) (x.getD k 0)).2 < 2 ^ 64 := by
      refine ⟨mulWW_spec _ _, ?_, Nat.mod_lt _ (by omega)⟩
      show x.getD k 0 * x.getD k 0 / 2 ^ 64 < 2 ^ 64
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.mul_lt_mul'' hd hd
    generalize hp : mulWW (x.getD k 0) (x.getD k 0) = p at *
    obtain ⟨ph, pl⟩ := p
    simp only [] at m1 m2 m3 ⊢
    have hl2 : [pl, ph].length = 2 := rfl
    have hzu : (upd z (2 * k) [pl, ph]).length = z.length := length_upd _ _ _ (by rw [hl2]; omega)
    have hzW : Wd (upd z (2 * k) [pl, ph]) := Wd_upd hz (Wd_cons.2 ⟨m3, Wd_cons.2 ⟨m2, Wd_nil⟩⟩)
    have hzt : (upd z (2 * k) [pl, ph]).take (2 * (k + 1)) = z.take (2 * k) ++ [pl, ph] := by
      have := take_upd_exact z [pl, ph] (2 * k) (by rw [hl2]; omega)
      rw [hl2] at this
      rw [← this]; congr 1
    have hzd' : (upd z (2 * k) [pl, ph]).drop (2 * (k + 1)) = zi.drop (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      rw [drop_upd_far z [pl, ph] (2 * k) _ (by rw [hl2]; omega) (by rw [hl2]; omega)]
      have h := congrArg (List.drop 2) hzd
      rw [List.drop_drop, List.drop_drop] at h
      exact h
    have hvz : val ((upd z (2 * k) [pl, ph]).take (2 * (k + 1))) = val (z.take (2 * k)) + 2 ^ (64 * (2 * k)) * (x.getD k 0 * x.getD k 0) := by
      rw [hzt, val_append]
      have : (z.take (2 * k)).length = 2 * k := by simp [List.length_take]; omega
      rw [this]
      simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
      rw [← m1]; grind
    have hxs := val_take_succ x k hkn
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := basicSqrLoop_spec x hx zi f (k + 1) _ _ hzW s2 (hzu.trans hzl) (s1.trans htl)
      (by omega) (by omega) hzd'
      (by
        rw [show 2 * (k + 1) - 1 = k + k + 1 + 0 by omega, Nat.add_zero]
        rw [s4]; exact zero_drop_mono htd (by omega))
      (by
        intro e he
        have h5 : (addMulStep t (x.take k) k (x.getD k 0)).take 1 = t.take 1 := by
          have := congrArg (List.take 1) s5
          rw [List.take_take, List.take_take, Nat.min_eq_left (by omega)] at this
          exact this
        rw [h5] at he; exact ht1 e he)
      (by
        rw [hvz, hxs]
        have e1 : 2 ^ (64 * (2 * k)) = 2 ^ (64 * k) * 2 ^ (64 * k) := by rw [← Nat.pow_add]; congr 1; omega
        rw [e1]
        rw [show val (addMulStep t (x.take k) k (x.getD k 0)) = val t + 2 ^ (64 * k) * (val (x.take k) * x.getD k 0) from s3]
        generalize 2 ^ (64 * k) = P at *
        generalize val (x.take k) = A at *
        generalize val t = T at *
        generalize val (z.take (2 * k)) = Z at *
        generalize x.getD k 0 = d at *
        have : (A + P * d) ^ 2 = A ^ 2 + 2 * (P * (A * d)) + P * P * (d * d) := by grind
        rw [this, ← hv]
        grind)
    exact ⟨c1, c2, c3, c4, c5, c6, c7⟩

/-- `basicSqr` for `len(x) >= 12` (the doubling branch), `len(z) = 2 len(x)`: the result is `x*x`, whatever `z` held before. -/
theorem basicSqr_spec (z x : List Nat) (hz : Wd z) (hx : Wd x) (hn : 12 ≤ x.length) (hzl : z.length = 2 * x.length) :
    (basicSqr z x).length = 2 * x.length ∧ Wd (basicSqr z x) ∧ val (basicSqr z x) = val x * val x := by
  unfold basicSqr
  simp only []
  rw [if_neg (by omega)]
  generalize hn' : x.length = n at *
  have hx0 : x.getD 0 0 < 2 ^ 64 := by
    have : x.getD 0 0 ∈ x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp
    exact hx _ this
  obtain ⟨m1, m2, m3⟩ : (mulWW (x.getD 0 0) (x.getD 0 0)).1 * 2 ^ 64 + (mulWW (x.getD 0 0) (x.getD 0 0)).2 = x.getD 0 0 * x.getD 0 0 ∧
      (mulWW (x.getD 0 0) (x.getD 0 0)).1 < 2 ^ 64 ∧ (mulWW (x.getD 0 0) (x.getD 0 0)).2 < 2 ^ 64 := by
    refine ⟨mulWW_spec _ _, ?_, Nat.mod_lt _ (by omega)⟩
    show x.getD 0 0 * x.getD 0 0 / 2 ^ 64 < 2 ^ 64
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact Nat.mul_lt_mul'' hx0 hx0
  generalize hp : mulWW (x.getD 0 0) (x.getD 0 0) = p at *
  obtain ⟨ph, pl⟩ := p
  simp only [] at m1 m2 m3 ⊢
  have hl2 : [pl, ph].length = 2 := rfl
  have hzW : Wd (upd z 0 [pl, ph]) := Wd_upd hz (Wd_cons.2 ⟨m3, Wd_cons.2 ⟨m2, Wd_nil⟩⟩)
  have hzu : (upd z 0 [pl, ph]).length = z.length := length_upd _ _ _ (by rw [hl2]; omega)
  have hzd : (upd z 0 [pl, ph]).drop (2 * 1) = z.drop (2 * 1) :=
    drop_upd_far z [pl, ph] 0 _ (by rw [hl2]; omega) (by rw [hl2]; omega)
  have hzt : (upd z 0 [pl, ph]).take (2 * 1) = [pl, ph] := by
    have := take_upd_exact z [pl, ph] 0 (by rw [hl2]; omega)
    rw [hl2] at this; simpa using this
  have hx1 : x.take 1 = [x.getD 0 0] := by
    cases x with
    | nil => simp at hn'; omega
    | cons a as => simp
  have ht0 : ∀ e ∈ (List.replicate (2 * n) 0), e = 0 := fun e he => List.eq_of_mem_replicate he
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := basicSqrLoop_spec x hx z (n - 1) 1 _ _ hzW (Wd_replicate_zero _)
    (by omega) (by simp; omega) (by omega) (by omega) hzd
    (fun e he => ht0 e (List.mem_of_mem_drop he)) (fun e he => ht0 e (List.mem_of_mem_take he))
    (by
      rw [hzt, hx1, val_replicate_zero]
      simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
      grind)
  simp only [hn'] at c1 c2 c3 c4 c5 c6 c7
  generalize hL : basicSqrLoop x (n - 1) 1 (upd z 0 [pl, ph]) (List.replicate (2 * n) 0) = L at *
  obtain ⟨z1, t1⟩ := L
  simp only [] at c1 c2 c3 c4 c5 c6 c7 ⊢
  rw [List.take_of_length_le (by omega)] at c7
  have hsl : (sl t1 1 (2 * n - 2)).length = 2 * n - 2 := length_sl t1 1 _ (by omega)
  obtain ⟨l1, l2, l3, l4⟩ := lshVU_spec (sl t1 1 (2 * n - 2)) 1 (Wd_sl c4 _ _) (by omega) (by omega)
  rw [hsl] at l1 l4
  generalize hl : lshVU (sl t1 1 (2 * n - 2)) 1 = l at *
  obtain ⟨lv, lc⟩ := l
  simp only [] at l1 l2 l3 l4 ⊢
  -- t1 = B * val (sl t1 1 (2n-2))
  have hvt1 : val t1 = 2 ^ 64 * val (sl t1 1 (2 * n - 2)) := by
    have h1 := val_split t1 1 (by omega)
    have h2 : val (t1.take 1) = 0 := val_eq_zero_iff.2 (fun e he => c6 e he)
    have h3 := val_split (t1.drop 1) (2 * n - 2) (by simp; omega)
    have h4 : val ((t1.drop 1).drop (2 * n - 2)) = 0 := by
      apply val_eq_zero_iff.2
      intro e he
      apply c5
      rw [List.drop_drop] at he
      rw [show 2 * n - 1 = 1 + (2 * n - 2) by omega]; exact he
    have : (t1.drop 1).take (2 * n - 2) = sl t1 1 (2 * n - 2) := rfl
    rw [this, h4] at h3
    rw [h1, h2, h3]; simp
  have hu1len : (upd t1 1 lv).length = 2 * n := (length_upd _ _ _ (by omega)).trans c3
  have hu1 := val_upd t1 lv 1 (by omega)
  have hu1W : Wd (upd t1 1 lv) := Wd_upd c4 l2
  have hdr : (upd t1 1 lv).drop (2 * n - 1) = t1.drop (2 * n - 1) :=
    drop_upd_far t1 lv 1 _ (by omega) (by omega)
  have hslot : ((upd t1 1 lv).drop (2 * n - 1)).take [lc].length = [0] := by
    rw [hdr]
    have hne : t1.drop (2 * n - 1) ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    obtain ⟨h0, t0, hh⟩ : ∃ h0 t0, t1.drop (2 * n - 1) = h0 :: t0 := by
      cases h : t1.drop (2 * n - 1) with
      | nil => exact absurd h hne
      | cons h0 t0 => exact ⟨h0, t0, rfl⟩
    have : h0 = 0 := c5 h0 (by rw [hh]; simp)
    rw [hh, this]; simp
  have hu2 := val_upd (upd t1 1 lv) [lc] (2 * n - 1) (by rw [hu1len]; simp; omega)
  rw [hslot] at hu2
  have hlcW : Wd [lc] := Wd_cons.2 ⟨l3, Wd_nil⟩
  have hu2W : Wd (upd (upd t1 1 lv) (2 * n - 1) [lc]) := Wd_upd hu1W hlcW
  have hu2len : (upd (upd t1 1 lv) (2 * n - 1) [lc]).length = 2 * n :=
    (length_upd _ _ _ (by rw [hu1len]; simp; omega)).trans hu1len
  rw [l1] at hu1
  have hS : List.take (2 * n - 2) (List.drop 1 t1) = sl t1 1 (2 * n - 2) := rfl
  rw [hS] at hu1
  have hT2 : val (upd (upd t1 1 lv) (2 * n - 1) [lc]) = 2 * val t1 := by
    simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero] at hu2
    have e1 : 2 ^ (64 * (2 * n - 1)) = 2 ^ 64 * 2 ^ (64 * (2 * n - 2)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h5 := congrArg (fun t => 2 ^ 64 * t) l4
    simp only [Nat.mul_add, Nat.pow_one] at h5
    rw [e1] at hu2
    simp only [Nat.pow_one] at l4
    generalize 2 ^ (64 * (2 * n - 2)) = Q at *
    generalize val (upd t1 1 lv) = V1 at *
    generalize val (upd (upd t1 1 lv) (2 * n - 1) [lc]) = T2 at *
    generalize val (sl t1 1 (2 * n - 2)) = S at *
    generalize val lv = Lv at *
    generalize val t1 = T at *
    generalize 2 ^ 64 = B at *
    grind
  have hadd := addVVc_spec z1 (upd (upd t1 1 lv) (2 * n - 1) [lc]) 0 c2 hu2W (by omega) (by omega)
  have hvx : val x < 2 ^ (64 * n) := by rw [← hn']; exact val_lt hx
  have hxx : val x * val x < 2 ^ (64 * n) * 2 ^ (64 * n) := Nat.mul_lt_mul'' hvx hvx
  have e2 : 2 ^ (64 * (2 * n)) = 2 ^ (64 * n) * 2 ^ (64 * n) := by rw [← Nat.pow_add]; congr 1; omega
  obtain ⟨a1, a2, a3, a4⟩ := hadd
  show (addVVc z1 _ 0).1.length = 2 * n ∧ Wd (addVVc z1 _ 0).1 ∧ val (addVVc z1 _ 0).1 = _
  refine ⟨by rw [a1]; omega, a2, ?_⟩
  rw [hT2, c1, e2] at a4
  have hx2 : val x ^ 2 = val x * val x := by grind
  rw [hx2] at c7
  generalize 2 ^ (64 * n) * 2 ^ (64 * n) = Q at *
  generalize (addVVc z1 (upd (upd t1 1 lv) (2 * n - 1) [lc]) 0).2 = c at *
  generalize val x * val x = XX at *
  generalize val (addVVc z1 (upd (upd t1 1 lv) (2 * n - 1) [lc]) 0).1 = R at *
  have : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · have : Q * 1 ≤ Q * c := Nat.mul_le_mul_left _ h
      omega
  subst this
  omega

/-! ## nat.sqr -/

/-- basicSqrThreshold, karatsubaSqrThreshold (natmul.go:68-69). -/
def basicSqrThreshold : Nat := 12
def karatsubaSqrThreshold : Nat := 80

/-- Contract of the kernel `karatsubaSqr(stk, z, x)` (natmul.go:257) as called by `sqr`: returns `z[0:2n]` (not normalised). -/
def KSqrContract (ksqr : List Nat → List Nat) : Prop :=
  ∀ x : List Nat, Wd x → karatsubaSqrThreshold ≤ x.length →
    (ksqr x).length = 2 * x.length ∧ Wd (ksqr x) ∧ val (ksqr x) = val x * val x

/-- natmul.go:73 `(z nat) sqr(stk, x)`.  `z.make(2n)` contents are irrelevant (all of `z[0:2n]` is overwritten): zeros are passed. -/
def natSqrP (ksqr : List Nat → List Nat) (x : List Nat) : List Nat :=
  let n := x.length
  if n = 0 then [] else
  if n = 1 then (let q := mulWW (x.getD 0 0) (x.getD 0 0); norm [q.2, q.1]) else
  if n < basicSqrThreshold ∧ n < karatsubaSqrThreshold then norm (basicMul x x) else
  if n < karatsubaSqrThreshold then norm (basicSqr (List.replicate (2 * n) 0) x) else
  norm (ksqr x)

theorem natSqrP_spec (ksqr : List Nat → List Nat) (hk : KSqrContract ksqr) : SqrContract (natSqrP ksqr) := by
  intro x hx
  unfold natSqrP
  simp only []
  by_cases h0 : x.length = 0
  · rw [if_pos h0]
    have : x = [] := List.length_eq_zero_iff.1 h0
    subst this
    exact ⟨Wd_nil, rfl, rfl, by simp⟩
  rw [if_neg h0]
  by_cases h1 : x.length = 1
  · rw [if_pos h1]
    have hx0 : x.getD 0 0 < 2 ^ 64 := by
      have : x.getD 0 0 ∈ x := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp
      exact hx _ this
    obtain ⟨m1, m2, m3⟩ : (mulWW (x.getD 0 0) (x.getD 0 0)).1 * 2 ^ 64 + (mulWW (x.getD 0 0) (x.getD 0 0)).2 = x.getD 0 0 * x.getD 0 0 ∧
        (mulWW (x.getD 0 0) (x.getD 0 0)).1 < 2 ^ 64 ∧ (mulWW (x.getD 0 0) (x.getD 0 0)).2 < 2 ^ 64 := by
      refine ⟨mulWW_spec _ _, ?_, Nat.mod_lt _ (by omega)⟩
      show x.getD 0 0 * x.getD 0 0 / 2 ^ 64 < 2 ^ 64
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.mul_lt_mul'' hx0 hx0
    generalize mulWW (x.getD 0 0) (x.getD 0 0) = p at *
    obtain ⟨ph, pl⟩ := p
    simp only [] at m1 m2 m3 ⊢
    have hW : Wd [pl, ph] := Wd_cons.2 ⟨m3, Wd_cons.2 ⟨m2, Wd_nil⟩⟩
    have hv : val x = x.getD 0 0 := by
      cases x with
      | nil => simp at h1
      | cons a as =>
        have : as = [] := List.length_eq_zero_iff.1 (by simpa using h1)
        subst this; simp
    refine ⟨Wd_norm hW, ?_, normed_norm _, ?_⟩
    · rw [val_norm, hv]; simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]; grind
    · exact Nat.le_trans (length_norm_le _) (by simp; omega)
  rw [if_neg h1]
  by_cases h2 : x.length < basicSqrThreshold ∧ x.length < karatsubaSqrThreshold
  · rw [if_pos h2]
    obtain ⟨a, b, c⟩ := basicMul_spec x x hx hx
    exact ⟨Wd_norm b, by rw [val_norm, c], normed_norm _, Nat.le_trans (length_norm_le _) (by omega)⟩
  rw [if_neg h2]
  by_cases h3 : x.length < karatsubaSqrThreshold
  · rw [if_pos h3]
    have h12 : 12 ≤ x.length := by unfold basicSqrThreshold at h2; omega
    obtain ⟨a, b, c⟩ := basicSqr_spec (List.replicate (2 * x.length) 0) x (Wd_replicate_zero _) hx h12 (by simp)
    exact ⟨Wd_norm b, by rw [val_norm, c], normed_norm _, Nat.le_trans (length_norm_le _) (by omega)⟩
  · rw [if_neg h3]
    obtain ⟨a, b, c⟩ := hk x hx (by omega)
    exact ⟨Wd_norm b, by rw [val_norm, c], normed_norm _, Nat.le_trans (length_norm_le _) (by omega)⟩

end FvModexp.Mdl
