import FvModexp.Proofs.Common.Words
/-!
# Vector operations of `math/big` (arith.go, arith_decl.go) as functions on limb lists

Each model returns the new contents of the destination slice `z` (same length as the inputs) and the carry.
Elementwise loops read `x[i]`, `y[i]` before writing `z[i]` (and the machine code does the same), so the result is
independent of whether `z` aliases `x` (or `y`) exactly (`z == x` as slices); this is the "elementwise-alias" fact the callers
use (`addTo`, `basicMul`, `divBasic`).  All lengths are equal (Go panics / the assembly assumes it): theorems carry `x.length = y.length`.

* `addVVc`/`addVV`     arith.go:61   (`addVV_g`; machine code: arith_amd64.s / arith_arm64.s `addVV`)
* `subVVc`/`subVV`     arith.go:77   (`subVV_g`)
* `addVW`              arith.go:105  (early-exit carry propagation, copies the tail)
* `subVW`              arith.go:155
* `lshVU`              arith.go:196  (`lshVU_g`; for `s != 0`; the callers never pass `s == 0` to `lshVU`, `shlVU` handles it)
* `rshVU`              arith.go:217
* `mulAddVWW`          arith.go:237  (`mulAddVWW_g`)
* `addMulVVWW`         arith.go:249  (`addMulVVWW_g`)
-/
namespace FvModexp.Mdl

/-! ## addVV / subVV -/

def addVVc : List Nat → List Nat → Nat → List Nat × Nat
  | x :: xs, y :: ys, c =>
    let r := addc x y c
    let t := addVVc xs ys r.2
    (r.1 :: t.1, t.2)
  | _, _, c => ([], c)

/-- `addVV(z, x, y)`: z = x + y, returns the carry. -/
def addVV (x y : List Nat) : List Nat × Nat := addVVc x y 0

def subVVc : List Nat → List Nat → Nat → List Nat × Nat
  | x :: xs, y :: ys, c =>
    let r := subb x y c
    let t := subVVc xs ys r.2
    (r.1 :: t.1, t.2)
  | _, _, c => ([], c)

/-- `subVV(z, x, y)`: z = x - y, returns the borrow. -/
def subVV (x y : List Nat) : List Nat × Nat := subVVc x y 0

theorem addVVc_spec : ∀ (x y : List Nat) (c : Nat), Wd x → Wd y → x.length = y.length → c ≤ 1 →
    (addVVc x y c).1.length = x.length ∧ Wd (addVVc x y c).1 ∧ (addVVc x y c).2 ≤ 1 ∧
    val (addVVc x y c).1 + 2 ^ (64 * x.length) * (addVVc x y c).2 = val x + val y + c
  | [], [], c, _, _, _, hc => by simp [addVVc, Wd_nil]; exact hc
  | [], _ :: _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | x :: xs, y :: ys, c, hx, hy, hl, hc => by
    have hxd := Wd_cons.1 hx
    have hyd := Wd_cons.1 hy
    have hl' : xs.length = ys.length := by simpa using hl
    have hr : addc x y c = ((x + y + c) % 2 ^ 64, (x + y + c) / 2 ^ 64) := rfl
    have ih := addVVc_spec xs ys (addc x y c).2 hxd.2 hyd.2 hl' (by rw [hr]; simp only []; omega)
    obtain ⟨i1, i2, i3, i4⟩ := ih
    simp only [addVVc]
    refine ⟨by simp [i1], ?_, i3, ?_⟩
    · exact Wd_cons.2 ⟨by rw [hr]; simp only []; exact Nat.mod_lt _ (by omega), i2⟩
    · simp only [List.length_cons, val_cons]
      rw [hr] at i4 ⊢
      simp only [] at i4 ⊢
      have e : 2 ^ (64 * (xs.length + 1)) = 2 ^ 64 * 2 ^ (64 * xs.length) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
      rw [e]
      have : 2 ^ 64 * (val (addVVc xs ys ((x + y + c) / 2 ^ 64)).1) + 2 ^ 64 * (2 ^ (64 * xs.length) * (addVVc xs ys ((x + y + c) / 2 ^ 64)).2)
          = 2 ^ 64 * (val xs + val ys + (x + y + c) / 2 ^ 64) := by
        rw [← Nat.mul_add, i4]
      have hq := Nat.div_add_mod (x + y + c) (2 ^ 64)
      grind

theorem subVVc_spec : ∀ (x y : List Nat) (c : Nat), Wd x → Wd y → x.length = y.length → c ≤ 1 →
    (subVVc x y c).1.length = x.length ∧ Wd (subVVc x y c).1 ∧ (subVVc x y c).2 ≤ 1 ∧
    val (subVVc x y c).1 + val y + c = val x + 2 ^ (64 * x.length) * (subVVc x y c).2
  | [], [], c, _, _, _, hc => by simp [subVVc, Wd_nil]; exact hc
  | [], _ :: _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | x :: xs, y :: ys, c, hx, hy, hl, hc => by
    have hxd := Wd_cons.1 hx
    have hyd := Wd_cons.1 hy
    have hl' : xs.length = ys.length := by simpa using hl
    have hr : subb x y c = ((x + 2 ^ 64 - y - c) % 2 ^ 64, if x < y + c then 1 else 0) := rfl
    have hb : (subb x y c).2 ≤ 1 := by rw [hr]; simp only []; split <;> omega
    have ih := subVVc_spec xs ys (subb x y c).2 hxd.2 hyd.2 hl' hb
    obtain ⟨i1, i2, i3, i4⟩ := ih
    simp only [subVVc]
    refine ⟨by simp [i1], ?_, i3, ?_⟩
    · exact Wd_cons.2 ⟨by rw [hr]; simp only []; exact Nat.mod_lt _ (by omega), i2⟩
    · simp only [List.length_cons, val_cons]
      rw [hr] at i4 ⊢
      simp only [] at i4 ⊢
      have e : 2 ^ (64 * (xs.length + 1)) = 2 ^ 64 * 2 ^ (64 * xs.length) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
      rw [e]
      have hz : (x + 2 ^ 64 - y - c) % 2 ^ 64 + y + c = x + 2 ^ 64 * (if x < y + c then 1 else 0) := by
        split <;> omega
      rw [Nat.mul_assoc]
      by_cases hb : x < y + c <;> simp only [hb, ite_true, ite_false] at hz i4 ⊢ <;> omega

/-! ## addVW / subVW -/

/-- Carry propagation of `+1` through the tail of `addVW` (the `for i := 1; ...` loop): `0xFF..` limbs become 0. -/
def incCarry : List Nat → List Nat × Nat
  | [] => ([], 1)
  | x :: xs => if x = 2 ^ 64 - 1 then (let t := incCarry xs; (0 :: t.1, t.2)) else ((x + 1) :: xs, 0)

/-- Borrow propagation of `-1` through the tail of `subVW`. -/
def decCarry : List Nat → List Nat × Nat
  | [] => ([], 1)
  | x :: xs => if x = 0 then (let t := decCarry xs; ((2 ^ 64 - 1) :: t.1, t.2)) else ((x - 1) :: xs, 0)

/-- arith.go:105 `addVW(z, x, y)`: z = x + y, returns the final carry (`y` itself if `len(z) == 0`). -/
def addVW : List Nat → Nat → List Nat × Nat
  | [], y => ([], y)
  | x0 :: xs, y =>
    let r := addc x0 y 0
    if r.2 = 0 then (r.1 :: xs, 0) else (let t := incCarry xs; (r.1 :: t.1, t.2))

/-- arith.go:155 `subVW(z, x, y)`: z = x - y, returns the final borrow (`y` itself if `len(z) == 0`). -/
def subVW : List Nat → Nat → List Nat × Nat
  | [], y => ([], y)
  | x0 :: xs, y =>
    let r := subb x0 y 0
    if r.2 = 0 then (r.1 :: xs, 0) else (let t := decCarry xs; (r.1 :: t.1, t.2))

theorem pow_succ64 (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]

theorem incCarry_spec : ∀ (xs : List Nat), Wd xs →
    (incCarry xs).1.length = xs.length ∧ Wd (incCarry xs).1 ∧ (incCarry xs).2 ≤ 1 ∧
    val (incCarry xs).1 + 2 ^ (64 * xs.length) * (incCarry xs).2 = val xs + 1
  | [], _ => by simp [incCarry, Wd_nil]
  | x :: xs, hx => by
    have hxd := Wd_cons.1 hx
    unfold incCarry
    by_cases h : x = 2 ^ 64 - 1
    · rw [if_pos h]
      obtain ⟨i1, i2, i3, i4⟩ := incCarry_spec xs hxd.2
      refine ⟨by simp [i1], Wd_cons.2 ⟨by decide, i2⟩, i3, ?_⟩
      simp only [List.length_cons, val_cons, pow_succ64]
      subst h
      generalize (incCarry xs).2 = c at *
      generalize val (incCarry xs).1 = Z at *
      have : 2 ^ 64 * Z + 2 ^ 64 * (2 ^ (64 * xs.length) * c) = 2 ^ 64 * (val xs + 1) := by
        rw [← Nat.mul_add, i4]
      rw [Nat.mul_assoc]
      omega
    · rw [if_neg h]
      refine ⟨by simp, Wd_cons.2 ⟨by omega, hxd.2⟩, by omega, ?_⟩
      simp only [List.length_cons, val_cons]
      omega

theorem decCarry_spec : ∀ (xs : List Nat), Wd xs →
    (decCarry xs).1.length = xs.length ∧ Wd (decCarry xs).1 ∧ (decCarry xs).2 ≤ 1 ∧
    val (decCarry xs).1 + 1 = val xs + 2 ^ (64 * xs.length) * (decCarry xs).2
  | [], _ => by simp [decCarry, Wd_nil]
  | x :: xs, hx => by
    have hxd := Wd_cons.1 hx
    unfold decCarry
    by_cases h : x = 0
    · rw [if_pos h]
      obtain ⟨i1, i2, i3, i4⟩ := decCarry_spec xs hxd.2
      refine ⟨by simp [i1], Wd_cons.2 ⟨by decide, i2⟩, i3, ?_⟩
      simp only [List.length_cons, val_cons, pow_succ64]
      subst h
      generalize (decCarry xs).2 = c at *
      generalize val (decCarry xs).1 = Z at *
      have : 2 ^ 64 * (Z + 1) = 2 ^ 64 * (val xs + 2 ^ (64 * xs.length) * c) := by rw [i4]
      rw [Nat.mul_add, Nat.mul_add] at this
      rw [Nat.mul_assoc]
      omega
    · rw [if_neg h]
      refine ⟨by simp, Wd_cons.2 ⟨by omega, hxd.2⟩, by omega, ?_⟩
      simp only [List.length_cons, val_cons]
      omega

theorem addVW_spec (x : List Nat) (y : Nat) (hx : Wd x) (hy : y < 2 ^ 64) :
    (addVW x y).1.length = x.length ∧ Wd (addVW x y).1 ∧ (x ≠ [] → (addVW x y).2 ≤ 1) ∧ (x = [] → (addVW x y).2 = y) ∧
    val (addVW x y).1 + 2 ^ (64 * x.length) * (addVW x y).2 = val x + y := by
  cases x with
  | nil => simp [addVW, Wd_nil]
  | cons x0 xs =>
    have hxd := Wd_cons.1 hx
    have hc : (addc x0 y 0).2 = (x0 + y) / 2 ^ 64 := rfl
    have hz : (addc x0 y 0).1 = (x0 + y) % 2 ^ 64 := rfl
    dsimp only [addVW]
    split
    · rename_i h
      refine ⟨by simp, Wd_cons.2 ⟨by rw [hz]; exact Nat.mod_lt _ (by omega), hxd.2⟩, by simp, by simp, ?_⟩
      simp only [List.length_cons, val_cons, pow_succ64]
      rw [hc] at h; rw [hz]
      omega
    · rename_i h
      obtain ⟨i1, i2, i3, i4⟩ := incCarry_spec xs hxd.2
      refine ⟨by simp [i1], Wd_cons.2 ⟨by rw [hz]; exact Nat.mod_lt _ (by omega), i2⟩, by simp [i3], by simp, ?_⟩
      simp only [List.length_cons, val_cons, pow_succ64]
      rw [hc] at h; rw [hz]
      generalize (incCarry xs).2 = c at *
      generalize val (incCarry xs).1 = Z at *
      have : 2 ^ 64 * (Z + 2 ^ (64 * xs.length) * c) = 2 ^ 64 * (val xs + 1) := by rw [i4]
      rw [Nat.mul_add] at this
      rw [Nat.mul_assoc]
      omega

theorem subVW_spec (x : List Nat) (y : Nat) (hx : Wd x) (hy : y < 2 ^ 64) :
    (subVW x y).1.length = x.length ∧ Wd (subVW x y).1 ∧ (x ≠ [] → (subVW x y).2 ≤ 1) ∧ (x = [] → (subVW x y).2 = y) ∧
    val (subVW x y).1 + y = val x + 2 ^ (64 * x.length) * (subVW x y).2 := by
  cases x with
  | nil => simp [subVW, Wd_nil]
  | cons x0 xs =>
    have hxd := Wd_cons.1 hx
    have hc : (subb x0 y 0).2 = if x0 < y + 0 then 1 else 0 := rfl
    have hz : (subb x0 y 0).1 = (x0 + 2 ^ 64 - y - 0) % 2 ^ 64 := rfl
    dsimp only [subVW]
    split
    · rename_i h
      refine ⟨by simp, Wd_cons.2 ⟨by rw [hz]; exact Nat.mod_lt _ (by omega), hxd.2⟩, by simp, by simp, ?_⟩
      simp only [List.length_cons, val_cons, pow_succ64]
      rw [hc] at h; rw [hz]
      split at h <;> omega
    · rename_i h
      obtain ⟨i1, i2, i3, i4⟩ := decCarry_spec xs hxd.2
      refine ⟨by simp [i1], Wd_cons.2 ⟨by rw [hz]; exact Nat.mod_lt _ (by omega), i2⟩, by simp [i3], by simp, ?_⟩
      simp only [List.length_cons, val_cons, pow_succ64]
      rw [hc] at h; rw [hz]
      generalize (decCarry xs).2 = c at *
      generalize val (decCarry xs).1 = Z at *
      have : 2 ^ 64 * (Z + 1) = 2 ^ 64 * (val xs + 2 ^ (64 * xs.length) * c) := by rw [i4]
      rw [Nat.mul_add, Nat.mul_add] at this
      rw [Nat.mul_assoc]
      split at h <;> omega

/-! ## shifts -/

theorem shl_split (a s : Nat) (hs : s ≤ 64) :
    a * 2 ^ s = (a / 2 ^ (64 - s)) * 2 ^ 64 + a * 2 ^ s % 2 ^ 64 := by
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
  have hq : a * 2 ^ s / 2 ^ 64 = a / 2 ^ (64 - s) := by
    rw [e, Nat.mul_comm (2 ^ (64 - s)), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hp]
  have := Nat.div_add_mod (a * 2 ^ s) (2 ^ 64)
  rw [hq] at this
  omega

theorem shl_mod (a s : Nat) (hs : s ≤ 64) : a * 2 ^ s % 2 ^ 64 = 2 ^ s * (a % 2 ^ (64 - s)) := by
  have e : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.mul_comm a, e, Nat.mul_mod_mul_left]

theorem shl_or (a p s : Nat) (hs : s ≤ 63) (hp : p < 2 ^ 64) :
    (a * 2 ^ s % 2 ^ 64) ||| (p / 2 ^ (64 - s)) = a * 2 ^ s % 2 ^ 64 + p / 2 ^ (64 - s) := by
  have hlt : p / 2 ^ (64 - s) < 2 ^ s := by
    have e : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
    apply Nat.div_lt_of_lt_mul
    rw [← e]; exact hp
  rw [shl_mod a s (by omega), ← Nat.two_pow_add_eq_or_of_lt hlt]

/-- Loop body of `lshVU_g`: `z[i] = x[i]<<s | x[i-1]>>ŝ` (`prev` is `x[i-1]`, 0 for `i = 0`). -/
def lshVUz (s : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | prev, x :: xs => ((x * 2 ^ s % 2 ^ 64) ||| (prev / 2 ^ (64 - s))) :: lshVUz s x xs

/-- arith.go:196 `lshVU_g(z, x, s)`: z = x << s, returns the bits shifted out (`c = x[n-1] >> ŝ`). -/
def lshVU (x : List Nat) (s : Nat) : List Nat × Nat :=
  if s = 0 then (x, 0) else (lshVUz s 0 x, (x.getLast?.getD 0) / 2 ^ (64 - s))

theorem getLast?_getD_cons (b : Nat) (bs : List Nat) (d d' : Nat) :
    (b :: bs).getLast?.getD d = (b :: bs).getLast?.getD d' := by
  rw [List.getLast?_eq_getLast (by simp : b :: bs ≠ [])]; rfl

theorem lshVUz_spec (s : Nat) (hs : s ≤ 63) : ∀ (x : List Nat) (prev : Nat), Wd x → prev < 2 ^ 64 →
    (lshVUz s prev x).length = x.length ∧ Wd (lshVUz s prev x) ∧
    val (lshVUz s prev x) + 2 ^ (64 * x.length) * ((x.getLast?.getD prev) / 2 ^ (64 - s)) =
      val x * 2 ^ s + prev / 2 ^ (64 - s)
  | [], prev, _, _ => by simp [lshVUz, Wd_nil]
  | a :: as, prev, hx, hp => by
    have hxd := Wd_cons.1 hx
    obtain ⟨i1, i2, i4⟩ := lshVUz_spec s hs as a hxd.2 hxd.1
    have hlast : (a :: as).getLast?.getD prev = as.getLast?.getD a := by
      cases as with
      | nil => simp
      | cons b bs => exact getLast?_getD_cons b bs prev a
    unfold lshVUz
    rw [shl_or a prev s hs hp]
    refine ⟨by simp [i1], ?_, ?_⟩
    · refine Wd_cons.2 ⟨?_, i2⟩
      have := shl_or a prev s hs hp
      rw [← this]
      -- both operands are below 2^64, so is the or
      have hlt : (a * 2 ^ s % 2 ^ 64) ||| (prev / 2 ^ (64 - s)) < 2 ^ 64 := Nat.or_lt_two_pow (Nat.mod_lt _ (by omega)) (by
        have : prev / 2 ^ (64 - s) ≤ prev := Nat.div_le_self _ _
        omega)
      exact hlt
    · rw [hlast]
      simp only [List.length_cons, val_cons, pow_succ64]
      have hsp := shl_split a s (by omega)
      generalize as.getLast?.getD a / 2 ^ (64 - s) = cc at *
      generalize val (lshVUz s a as) = Z at *
      generalize a / 2 ^ (64 - s) = h1 at *
      generalize prev / 2 ^ (64 - s) = h2 at *
      generalize a * 2 ^ s % 2 ^ 64 = lo at *
      have : 2 ^ 64 * (Z + 2 ^ (64 * as.length) * cc) = 2 ^ 64 * (val as * 2 ^ s + h1) := by rw [i4]
      rw [Nat.mul_add, Nat.mul_add] at this
      rw [Nat.mul_assoc]
      have e3 : val (a :: as) * 2 ^ s = a * 2 ^ s + 2 ^ 64 * (val as * 2 ^ s) := by
        simp only [val_cons]; grind
      grind

theorem lshVU_spec (x : List Nat) (s : Nat) (hx : Wd x) (hs1 : 1 ≤ s) (hs : s ≤ 63) :
    (lshVU x s).1.length = x.length ∧ Wd (lshVU x s).1 ∧ (lshVU x s).2 < 2 ^ 64 ∧
    val (lshVU x s).1 + 2 ^ (64 * x.length) * (lshVU x s).2 = val x * 2 ^ s := by
  unfold lshVU
  rw [if_neg (by omega)]
  obtain ⟨i1, i2, i4⟩ := lshVUz_spec s hs x 0 hx (by decide)
  simp only [Nat.zero_div, Nat.add_zero] at i4
  have hc : (x.getLast?.getD 0) / 2 ^ (64 - s) < 2 ^ 64 := by
    have : x.getLast?.getD 0 < 2 ^ 64 := by
      cases h : x.getLast? with
      | none => simp
      | some a => simp; exact hx a (List.mem_of_getLast? h)
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this
  exact ⟨i1, i2, hc, i4⟩

/-- Loop body of `rshVU_g`: `z[i-1] = x[i-1]>>s | x[i]<<ŝ`, `z[n-1] = x[n-1]>>s`. -/
def rshVUz (s : Nat) : List Nat → List Nat
  | [] => []
  | [x] => [x / 2 ^ s]
  | x :: y :: ys => ((x / 2 ^ s) ||| (y * 2 ^ (64 - s) % 2 ^ 64)) :: rshVUz s (y :: ys)

/-- arith.go:217 `rshVU_g(z, x, s)`: z = x >> s, returns the bits shifted out (`c = x[0] << ŝ`). -/
def rshVU (x : List Nat) (s : Nat) : List Nat × Nat :=
  if s = 0 then (x, 0) else (rshVUz s x, match x with | [] => 0 | x0 :: _ => x0 * 2 ^ (64 - s) % 2 ^ 64)

theorem rshVUz_spec (s : Nat) (hs1 : 1 ≤ s) (hs : s ≤ 63) : ∀ (x : List Nat), Wd x → x ≠ [] →
    (rshVUz s x).length = x.length ∧ Wd (rshVUz s x) ∧ val (rshVUz s x) = val x / 2 ^ s
  | [], _, h => absurd rfl h
  | [x], hx, _ => by
    have := (Wd_cons.1 hx).1
    refine ⟨by simp [rshVUz], Wd_cons.2 ⟨Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this, Wd_nil⟩, by simp [rshVUz]⟩
  | x :: y :: ys, hx, _ => by
    have hxd := Wd_cons.1 hx
    have hyd := Wd_cons.1 hxd.2
    obtain ⟨i1, i2, i3⟩ := rshVUz_spec s hs1 hs (y :: ys) hxd.2 (by simp)
    have hm : 0 < 2 ^ s := Nat.two_pow_pos s
    have hk : 0 < 2 ^ (64 - s) := Nat.two_pow_pos _
    have hB : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
    have hlt : x / 2 ^ s < 2 ^ (64 - s) := by
      apply Nat.div_lt_of_lt_mul
      rw [← hB]; exact hxd.1
    have hmod : y * 2 ^ (64 - s) % 2 ^ 64 = 2 ^ (64 - s) * (y % 2 ^ s) := by
      rw [Nat.mul_comm y, hB, Nat.mul_comm (2 ^ s), Nat.mul_mod_mul_left]
    have hor : (x / 2 ^ s) ||| (y * 2 ^ (64 - s) % 2 ^ 64) = x / 2 ^ s + y * 2 ^ (64 - s) % 2 ^ 64 := by
      rw [hmod, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hlt, Nat.add_comm]
    have hz0 : (x / 2 ^ s + y * 2 ^ (64 - s) % 2 ^ 64) < 2 ^ 64 := by
      rw [hmod]
      have : y % 2 ^ s < 2 ^ s := Nat.mod_lt _ hm
      have : 2 ^ (64 - s) * (y % 2 ^ s) + 2 ^ (64 - s) ≤ 2 ^ (64 - s) * 2 ^ s := by
        have := Nat.mul_le_mul_left (2 ^ (64 - s)) (Nat.succ_le_of_lt this)
        rw [Nat.mul_succ] at this; exact this
      rw [hB, Nat.mul_comm (2 ^ s)]
      omega
    unfold rshVUz
    rw [hor]
    refine ⟨by simp [i1], Wd_cons.2 ⟨hz0, i2⟩, ?_⟩
    simp only [val_cons] at i3 ⊢
    rw [i3]
    -- (x + B*T)/m = x/m + k*T   and   T/m = y/m + k*val ys
    generalize hT : y + 2 ^ 64 * val ys = T
    have h1 : (x + 2 ^ 64 * T) / 2 ^ s = x / 2 ^ s + 2 ^ (64 - s) * T := by
      have : 2 ^ 64 * T = 2 ^ s * (2 ^ (64 - s) * T) := by rw [hB, Nat.mul_assoc]
      rw [this, Nat.add_mul_div_left _ _ hm]
    rw [h1]
    have h2 : T / 2 ^ s = y / 2 ^ s + 2 ^ (64 - s) * val ys := by
      have : T = y + 2 ^ s * (2 ^ (64 - s) * val ys) := by rw [← hT, hB, Nat.mul_assoc]
      rw [this, Nat.add_mul_div_left _ _ hm]
    rw [h2, hmod]
    have hy := Nat.div_add_mod y (2 ^ s)
    have hTy : T = y + 2 ^ 64 * val ys := hT.symm
    clear h1 h2 hT i3
    generalize y / 2 ^ s = yh at *
    generalize y % 2 ^ s = yl at *
    generalize 2 ^ s = m at *
    generalize 2 ^ (64 - s) = k at *
    generalize x / m = xh at *
    have hBk : 2 ^ 64 = m * k := hB
    rw [hTy, hBk, ← hy]
    grind

theorem rshVU_spec (x : List Nat) (s : Nat) (hx : Wd x) (hs1 : 1 ≤ s) (hs : s ≤ 63) :
    (rshVU x s).1.length = x.length ∧ Wd (rshVU x s).1 ∧ val (rshVU x s).1 = val x / 2 ^ s ∧
    (rshVU x s).2 = (val x % 2 ^ s) * 2 ^ (64 - s) := by
  unfold rshVU
  rw [if_neg (by omega)]
  cases x with
  | nil => simp [rshVUz, Wd_nil]
  | cons x0 xs =>
    obtain ⟨i1, i2, i3⟩ := rshVUz_spec s hs1 hs (x0 :: xs) hx (by simp)
    refine ⟨i1, i2, i3, ?_⟩
    simp only []
    have hB : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
    have hm : 0 < 2 ^ s := Nat.two_pow_pos s
    -- val x % 2^s = x0 % 2^s since 2^s | 2^64
    have : val (x0 :: xs) % 2 ^ s = x0 % 2 ^ s := by
      simp only [val_cons]
      rw [hB, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    rw [this, Nat.mul_comm x0, hB, Nat.mul_comm (2 ^ s), Nat.mul_mod_mul_left, Nat.mul_comm]

/-! ## multiply-accumulate -/

/-- arith.go:237 `mulAddVWW_g(z, x, y, r)`: z = x*y + r, returns the carry word. -/
def mulAddVWW : List Nat → Nat → Nat → List Nat × Nat
  | [], _, r => ([], r)
  | x :: xs, y, r =>
    let p := mulAddWWW x y r
    let t := mulAddVWW xs y p.1
    (p.2 :: t.1, t.2)

/-- arith.go:249 `addMulVVWW_g(z, x, y, m, a)`: z = x + y*m + a, returns the carry word. -/
def addMulVVWW : List Nat → List Nat → Nat → Nat → List Nat × Nat
  | x :: xs, y :: ys, m, c =>
    let p := mulAddWWW y m x                       -- z1, z0 := mulAddWWW_g(y[i], m, x[i])
    let q := addc p.2 c 0                          -- lo, cc := bits.Add(z0, c, 0)
    let c' := (q.2 + p.1) % 2 ^ 64                 -- c, z[i] = cc, lo; c += z1
    let t := addMulVVWW xs ys m c'
    (q.1 :: t.1, t.2)
  | _, _, _, c => ([], c)

theorem mulAddVWW_spec : ∀ (x : List Nat) (y r : Nat), Wd x → y < 2 ^ 64 → r < 2 ^ 64 →
    (mulAddVWW x y r).1.length = x.length ∧ Wd (mulAddVWW x y r).1 ∧ (mulAddVWW x y r).2 < 2 ^ 64 ∧
    val (mulAddVWW x y r).1 + 2 ^ (64 * x.length) * (mulAddVWW x y r).2 = val x * y + r
  | [], y, r, _, _, hr => by simp [mulAddVWW, Wd_nil, hr]
  | x :: xs, y, r, hx, hy, hr => by
    have hxd := Wd_cons.1 hx
    obtain ⟨p1, p2, p3⟩ := mulAddWWW_spec x y r hxd.1 hy hr
    obtain ⟨i1, i2, i3, i4⟩ := mulAddVWW_spec xs y (mulAddWWW x y r).1 hxd.2 hy p2
    unfold mulAddVWW
    simp only []
    refine ⟨by simp [i1], Wd_cons.2 ⟨p3, i2⟩, i3, ?_⟩
    simp only [List.length_cons, val_cons, pow_succ64]
    generalize (mulAddVWW xs y (mulAddWWW x y r).1).2 = c at *
    generalize val (mulAddVWW xs y (mulAddWWW x y r).1).1 = Z at *
    generalize (mulAddWWW x y r).1 = h1 at *
    generalize (mulAddWWW x y r).2 = l1 at *
    have : 2 ^ 64 * (Z + 2 ^ (64 * xs.length) * c) = 2 ^ 64 * (val xs * y + h1) := by rw [i4]
    rw [Nat.mul_add, Nat.mul_add] at this
    rw [Nat.mul_assoc]
    grind

theorem addMulVVWW_spec : ∀ (x y : List Nat) (m c : Nat), Wd x → Wd y → x.length = y.length → m < 2 ^ 64 → c < 2 ^ 64 →
    (addMulVVWW x y m c).1.length = x.length ∧ Wd (addMulVVWW x y m c).1 ∧ (addMulVVWW x y m c).2 < 2 ^ 64 ∧
    val (addMulVVWW x y m c).1 + 2 ^ (64 * x.length) * (addMulVVWW x y m c).2 = val x + val y * m + c
  | [], [], m, c, _, _, _, _, hc => by simp [addMulVVWW, Wd_nil, hc]
  | [], _ :: _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _ => by simp at h
  | x :: xs, y :: ys, m, c, hx, hy, hl, hm, hc => by
    have hxd := Wd_cons.1 hx
    have hyd := Wd_cons.1 hy
    have hl' : xs.length = ys.length := by simpa using hl
    obtain ⟨p1, p2, p3⟩ := mulAddWWW_spec y m x hyd.1 hm hxd.1
    have hq : (addc (mulAddWWW y m x).2 c 0) = (((mulAddWWW y m x).2 + c + 0) % 2 ^ 64, ((mulAddWWW y m x).2 + c + 0) / 2 ^ 64) := rfl
    -- carry out < 2^64
    have hc' : ((addc (mulAddWWW y m x).2 c 0).2 + (mulAddWWW y m x).1) % 2 ^ 64 =
        (addc (mulAddWWW y m x).2 c 0).2 + (mulAddWWW y m x).1 := by
      apply Nat.mod_eq_of_lt
      rw [hq]; simp only []
      have : y * m ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      have h5 : (mulAddWWW y m x).1 * 2 ^ 64 + (mulAddWWW y m x).2 = y * m + x := p1
      generalize (mulAddWWW y m x).1 = h1 at *
      generalize (mulAddWWW y m x).2 = l1 at *
      omega
    obtain ⟨i1, i2, i3, i4⟩ := addMulVVWW_spec xs ys m ((addc (mulAddWWW y m x).2 c 0).2 + (mulAddWWW y m x).1) hxd.2 hyd.2 hl' hm (by
      rw [← hc']; exact Nat.mod_lt _ (by omega))
    unfold addMulVVWW
    simp only []
    rw [hc']
    refine ⟨by simp [i1], Wd_cons.2 ⟨by rw [hq]; exact Nat.mod_lt _ (by omega), i2⟩, i3, ?_⟩
    simp only [List.length_cons, val_cons, pow_succ64]
    rw [hq] at i4 ⊢
    simp only [Nat.add_zero] at i4 ⊢
    generalize (addMulVVWW xs ys m (((mulAddWWW y m x).2 + c) / 2 ^ 64 + (mulAddWWW y m x).1)).2 = cc at *
    generalize val (addMulVVWW xs ys m (((mulAddWWW y m x).2 + c) / 2 ^ 64 + (mulAddWWW y m x).1)).1 = Z at *
    generalize (mulAddWWW y m x).1 = h1 at *
    generalize (mulAddWWW y m x).2 = l1 at *
    have : 2 ^ 64 * (Z + 2 ^ (64 * xs.length) * cc) = 2 ^ 64 * (val xs + val ys * m + ((l1 + c) / 2 ^ 64 + h1)) := by rw [i4]
    rw [Nat.mul_add, Nat.mul_add] at this
    rw [Nat.mul_assoc]
    have hd := Nat.div_add_mod (l1 + c) (2 ^ 64)
    grind

end FvModexp.Mdl
