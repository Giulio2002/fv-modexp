import FvModexp.Proofs.Common.VecOps
/-!
# nat basics (nat.go): cmp, set*, add, sub, addTo, trunc, lsh, rsh

A Go `nat` is a `List Nat` (limbs, least significant first, `len` = length).  `z.make(n)` returns a slice of length `n` whose
old contents are irrelevant (every caller below overwrites all `n` limbs before reading), so the models take no `z`: they return the
final contents of the returned slice.  Capacity / aliasing of the *slice header* (whether the result reuses `z`'s backing array)
is a memory-model fact for the machine-code proofs; see docs/MODELS.md ("make contract").
Panics ("underflow", slice bounds) are not modelled; theorems carry the no-panic preconditions.

* `natCmp`      nat.go:152 `cmp`
* `natSetWord`  nat.go:71 `setWord`;  `natSetUint64` nat.go:80
* `natAdd`      nat.go:98 `add`;       `natSub` nat.go:124 `sub`
* `addTo`       nat.go:234 `addTo`
* `natTrunc`    nat.go:530 `trunc`;    `natLsh` nat.go:395;  `natRsh` nat.go:425
-/
namespace FvModexp.Mdl

/-! ## cmp -/

def cmpInt (a b : Nat) : Int := if a < b then -1 else if b < a then 1 else 0

/-- The comparison loop of `nat.cmp` (`i := m-1; for i > 0 && x[i] == y[i] { i-- }` ...), on most-significant-first lists. -/
def cmpRev : List Nat → List Nat → Int
  | [a], [b] => cmpInt a b
  | a :: a' :: as, b :: b' :: bs => if a = b then cmpRev (a' :: as) (b' :: bs) else cmpInt a b
  | _, _ => 0

/-- nat.go:152 `(x nat) cmp(y nat) (r int)`. -/
def natCmp (x y : List Nat) : Int :=
  if x.length ≠ y.length ∨ x.length = 0 then
    (if x.length < y.length then -1 else if x.length > y.length then 1 else 0)
  else cmpRev x.reverse y.reverse

/-- Most-significant-first value. -/
def msb : Nat → List Nat → Nat
  | acc, [] => acc
  | acc, d :: ds => msb (acc * 2 ^ 64 + d) ds

theorem cmpInt_lt {a b : Nat} (h : a < b) : cmpInt a b = -1 := by simp [cmpInt, h]
theorem cmpInt_gt {a b : Nat} (h : b < a) : cmpInt a b = 1 := by simp [cmpInt, h, Nat.not_lt.2 (Nat.le_of_lt h)]
theorem cmpInt_eq {a b : Nat} (h : a = b) : cmpInt a b = 0 := by simp [cmpInt, h]

theorem msb_acc (l : List Nat) : ∀ acc, msb acc l = acc * 2 ^ (64 * l.length) + msb 0 l := by
  induction l with
  | nil => intro acc; simp [msb]
  | cons d ds ih =>
    intro acc
    simp only [msb, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * 2 ^ 64 + d), ih d, List.length_cons, pow_succ64]
    rw [Nat.add_mul, Nat.mul_assoc]; grind

theorem val_reverse (l : List Nat) : val l.reverse = msb 0 l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [List.reverse_cons, val_append, ih]
    simp only [msb, Nat.zero_mul, Nat.zero_add, val_cons, List.length_reverse, val_nil, Nat.mul_zero, Nat.add_zero]
    rw [msb_acc ds d]
    grind

theorem msb_lt {l : List Nat} (h : Wd l) : msb 0 l < 2 ^ (64 * l.length) := by
  rw [← val_reverse]
  have := val_lt (l := l.reverse) (by intro d hd; exact h d (List.mem_reverse.1 hd))
  simpa using this

theorem cmpRev_spec : ∀ (a b : List Nat), Wd a → Wd b → a.length = b.length → a ≠ [] →
    cmpRev a b = cmpInt (msb 0 a) (msb 0 b)
  | [], _, _, _, _, h => absurd rfl h
  | [a], [b], _, _, _, _ => by simp [cmpRev, msb]
  | [_], _ :: _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _ :: _, [_], _, _, hl, _ => by simp at hl
  | _ :: _ :: _, [], _, _, hl, _ => by simp at hl
  | a :: a' :: as, b :: b' :: bs, ha, hb, hl, _ => by
    have had := Wd_cons.1 ha
    have hbd := Wd_cons.1 hb
    have hl' : (a' :: as).length = (b' :: bs).length := by simpa using hl
    have hlt1 := msb_lt had.2
    have hlt2 := msb_lt hbd.2
    have e1 := msb_acc (a' :: as) a
    have e2 := msb_acc (b' :: bs) b
    simp only [msb, Nat.zero_mul, Nat.zero_add] at e1 e2 hlt1 hlt2 ⊢
    have hl2 : as.length = bs.length := by simpa using hl'
    simp only [List.length_cons, hl2] at e1 e2 hlt1 hlt2
    unfold cmpRev
    rw [e1, e2]
    by_cases h : a = b
    · subst h
      rw [if_pos rfl]
      rw [cmpRev_spec (a' :: as) (b' :: bs) had.2 hbd.2 hl' (by simp)]
      simp only [msb, Nat.zero_mul, Nat.zero_add]
      generalize msb a' as = u at *
      generalize msb b' bs = v at *
      rcases Nat.lt_trichotomy u v with h | h | h
      · rw [cmpInt_lt h, cmpInt_lt (by omega)]
      · rw [cmpInt_eq h, cmpInt_eq (by omega)]
      · rw [cmpInt_gt h, cmpInt_gt (by omega)]
    · rw [if_neg h]
      generalize msb a' as = u at *
      generalize msb b' bs = v at *
      have hp : 0 < 2 ^ (64 * (bs.length + 1)) := Nat.two_pow_pos _
      generalize 2 ^ (64 * (bs.length + 1)) = P at *
      rcases Nat.lt_or_gt_of_ne h with hab | hab
      · have : (a + 1) * P ≤ b * P := Nat.mul_le_mul_right _ hab
        rw [Nat.add_mul] at this
        rw [cmpInt_lt hab, cmpInt_lt (by omega)]
      · have : (b + 1) * P ≤ a * P := Nat.mul_le_mul_right _ hab
        rw [Nat.add_mul] at this
        rw [cmpInt_gt hab, cmpInt_gt (by omega)]

/-- Correctness of `nat.cmp` for normalised operands. -/
theorem natCmp_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) (hnx : Normed x) (hny : Normed y) :
    natCmp x y = cmpInt (val x) (val y) := by
  unfold natCmp
  by_cases h : x.length ≠ y.length ∨ x.length = 0
  · rw [if_pos h]
    rcases h with h | h
    · rcases Nat.lt_or_gt_of_ne h with hl | hl
      · -- |x| < |y| : val x < 2^(64|x|) <= 2^(64(|y|-1)) <= val y
        have hyne : y ≠ [] := by intro e; rw [e] at hl; simp at hl
        have h1 := val_lt hx
        have h2 := hny.val_ge hyne hy
        have : 2 ^ (64 * x.length) ≤ 2 ^ (64 * (y.length - 1)) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        rw [if_pos hl, cmpInt_lt (by omega)]
      · have hxne : x ≠ [] := by intro e; rw [e] at hl; simp at hl
        have h1 := val_lt hx
        have h2 := hnx.val_ge hxne hx
        have : 2 ^ (64 * y.length) ≤ 2 ^ (64 * (x.length - 1)) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hl' : ¬ x.length < y.length := by omega
        rw [if_neg hl', if_pos hl, cmpInt_gt (by have := val_lt hy; omega)]
    · have hx0 : x = [] := List.length_eq_zero_iff.1 h
      -- x = [] and: if y = [] then equal, else |x| < |y|
      by_cases hy0 : y.length = 0
      · have : y = [] := List.length_eq_zero_iff.1 hy0
        subst hx0; subst this; simp [cmpInt]
      · have hyne : y ≠ [] := fun e => hy0 (by rw [e]; rfl)
        have h2 := hny.val_ge hyne hy
        have : 1 ≤ 2 ^ (64 * (y.length - 1)) := Nat.one_le_two_pow
        have hl : x.length < y.length := by omega
        subst hx0
        rw [if_pos hl, cmpInt_lt (by simp [val]; omega)]
  · rw [if_neg h]
    rw [not_or, Decidable.not_not] at h
    have hxne : x ≠ [] := fun e => h.2 (by rw [e]; rfl)
    rw [cmpRev_spec x.reverse y.reverse (fun d hd => hx d (List.mem_reverse.1 hd)) (fun d hd => hy d (List.mem_reverse.1 hd))
      (by simp [h.1]) (by simpa using hxne), ← val_reverse, ← val_reverse]
    simp

/-! ## setWord / setUint64 -/

/-- nat.go:71 `setWord`. -/
def natSetWord (x : Nat) : List Nat := if x = 0 then [] else [x]

/-- nat.go:80 `setUint64` (on a 64-bit `Word` the 2-word branch is dead; kept for faithfulness). -/
def natSetUint64 (x : Nat) : List Nat :=
  if x % 2 ^ 64 = x then natSetWord x else [x % 2 ^ 32, x / 2 ^ 32 % 2 ^ 64]

theorem natSetWord_spec (x : Nat) (h : x < 2 ^ 64) :
    val (natSetWord x) = x ∧ Wd (natSetWord x) ∧ Normed (natSetWord x) := by
  unfold natSetWord
  by_cases h0 : x = 0
  · subst h0; simp [Wd_nil, Normed]
  · rw [if_neg h0]
    refine ⟨by simp, Wd_cons.2 ⟨h, Wd_nil⟩, ?_⟩
    exact normed_cons.2 ⟨rfl, by simp [h0]⟩

theorem natSetUint64_spec (x : Nat) (h : x < 2 ^ 64) :
    natSetUint64 x = natSetWord x := by
  unfold natSetUint64; rw [if_pos (Nat.mod_eq_of_lt h)]

/-! ## add -/

/-- `nat.add` once `len(x) >= len(y)` (nat.go:98-121). -/
def natAddO (x y : List Nat) : List Nat :=
  let m := x.length
  let n := y.length
  if m = 0 then [] else
  if n = 0 then x else
  let r := addVV (x.take n) (y.take n)               -- c := addVV(z[:n], x[:n], y[:n])
  let hi := if m > n then addVW (x.drop n) r.2 else ([], r.2)   -- if m > n { c = addVW(z[n:m], x[n:], c) }
  norm (r.1 ++ hi.1 ++ [hi.2])                        -- z[m] = c; return z.norm()

/-- nat.go:98 `(z nat) add(x, y nat) nat` (the `m < n` case swaps the operands). -/
def natAdd (x y : List Nat) : List Nat := if x.length < y.length then natAddO y x else natAddO x y

theorem take_len_drop_val (x : List Nat) (n : Nat) (h : n ≤ x.length) :
    val x = val (x.take n) + 2 ^ (64 * n) * val (x.drop n) := val_split x n h

theorem natAddO_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) (hnx : Normed x) (hl : y.length ≤ x.length) :
    Wd (natAddO x y) ∧ val (natAddO x y) = val x + val y ∧ Normed (natAddO x y) := by
  unfold natAddO
  simp only []
  by_cases hm : x.length = 0
  · rw [if_pos hm]
    have hx0 : x = [] := List.length_eq_zero_iff.1 hm
    have hy0 : y = [] := List.length_eq_zero_iff.1 (by omega)
    subst hx0; subst hy0
    exact ⟨Wd_nil, rfl, rfl⟩
  rw [if_neg hm]
  by_cases hn : y.length = 0
  · rw [if_pos hn]
    have hy0 : y = [] := List.length_eq_zero_iff.1 hn
    subst hy0
    exact ⟨hx, by simp, hnx⟩
  rw [if_neg hn]
  rw [List.take_length]
  obtain ⟨i1, i2, i3, i4⟩ := addVVc_spec (x.take y.length) y 0 (hx.take _) hy (by simp; omega) (by omega)
  have hxs := take_len_drop_val x y.length hl
  have hlen : (x.take y.length).length = y.length := by simp; omega
  have hlo : (addVV (x.take y.length) y).1.length = y.length := by unfold addVV; rw [i1, hlen]
  have hsum : val (addVV (x.take y.length) y).1 + 2 ^ (64 * y.length) * (addVV (x.take y.length) y).2
      = val (x.take y.length) + val y := by
    unfold addVV; rw [hlen] at i4; omega
  have hc1 : (addVV (x.take y.length) y).2 ≤ 1 := i3
  have hwlo : Wd (addVV (x.take y.length) y).1 := i2
  generalize (addVV (x.take y.length) y).1 = lo at *
  generalize (addVV (x.take y.length) y).2 = c at *
  by_cases hgt : x.length > y.length
  · rw [if_pos hgt]
    have hxd : x.drop y.length ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    obtain ⟨j1, j2, j3, j4, j5⟩ := addVW_spec (x.drop y.length) c (hx.drop _) (by omega)
    generalize addVW (x.drop y.length) c = hh at *
    obtain ⟨hh1, hh2⟩ := hh
    have hl2 : (x.drop y.length).length = x.length - y.length := by simp
    simp only [hl2] at j1 j5
    have hc2 := j3 hxd
    have hw : Wd (lo ++ hh1 ++ [hh2]) := Wd_append.2 ⟨Wd_append.2 ⟨hwlo, j2⟩, by
      intro d hd; simp at hd; subst hd; omega⟩
    have hv : val (lo ++ hh1 ++ [hh2]) = val x + val y := by
      rw [val_append, val_append]
      simp only [List.length_append, val_cons, val_nil, hlo, j1, hl2]
      have e2 : 2 ^ (64 * (y.length + (x.length - y.length))) = 2 ^ (64 * y.length) * 2 ^ (64 * (x.length - y.length)) := by
        rw [← Nat.pow_add, ← Nat.mul_add]
      rw [e2]
      generalize 2 ^ (64 * y.length) = P at *
      generalize 2 ^ (64 * (x.length - y.length)) = Q at *
      have : P * (val hh1 + Q * hh2) = P * (val (x.drop y.length) + c) := by rw [j5]
      rw [Nat.mul_add, Nat.mul_add] at this
      have h3 : P * (Q * hh2) = P * Q * hh2 := by rw [Nat.mul_assoc]
      grind
    exact ⟨Wd_norm hw, by rw [val_norm]; exact hv, normed_norm _⟩
  · rw [if_neg hgt]
    have hxy : x.length = y.length := by omega
    have hw : Wd (lo ++ [] ++ [c]) := Wd_append.2 ⟨Wd_append.2 ⟨hwlo, Wd_nil⟩, by
      intro d hd; simp at hd; subst hd; omega⟩
    have hv : val (lo ++ [] ++ [c]) = val x + val y := by
      rw [val_append, val_append]
      simp only [List.length_append, val_cons, val_nil, hlo, List.length_nil, Nat.add_zero, Nat.mul_zero]
      have : x.drop y.length = [] := List.drop_of_length_le (by omega)
      rw [this] at hxs
      simp at hxs
      omega
    exact ⟨Wd_norm hw, by rw [val_norm]; exact hv, normed_norm _⟩

theorem natAdd_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) (hnx : Normed x) (hny : Normed y) :
    Wd (natAdd x y) ∧ val (natAdd x y) = val x + val y ∧ Normed (natAdd x y) := by
  unfold natAdd
  by_cases h : x.length < y.length
  · rw [if_pos h]
    have := natAddO_spec y x hy hx hny (by omega)
    exact ⟨this.1, by rw [this.2.1, Nat.add_comm], this.2.2⟩
  · rw [if_neg h]
    exact natAddO_spec x y hx hy hnx (by omega)

/-! ## sub -/

/-- `nat.sub` when `len(x) >= len(y)` (nat.go:124-149); the `c != 0` panic is not modelled. -/
def natSubO (x y : List Nat) : List Nat :=
  let m := x.length
  let n := y.length
  if m = 0 then [] else
  if n = 0 then x else
  let r := subVV (x.take n) (y.take n)
  let hi := if m > n then subVW (x.drop n) r.2 else ([], r.2)
  norm (r.1 ++ hi.1)

/-- nat.go:124 `(z nat) sub(x, y nat) nat`; `m < n` panics ("underflow"), modelled as `[]`. -/
def natSub (x y : List Nat) : List Nat := if x.length < y.length then [] else natSubO x y

theorem natSubO_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) (hnx : Normed x) (hl : y.length ≤ x.length)
    (hle : val y ≤ val x) :
    Wd (natSubO x y) ∧ val (natSubO x y) = val x - val y ∧ Normed (natSubO x y) := by
  unfold natSubO
  simp only []
  by_cases hm : x.length = 0
  · rw [if_pos hm]
    have hx0 : x = [] := List.length_eq_zero_iff.1 hm
    have hy0 : y = [] := List.length_eq_zero_iff.1 (by omega)
    subst hx0; subst hy0
    exact ⟨Wd_nil, rfl, rfl⟩
  rw [if_neg hm]
  by_cases hn : y.length = 0
  · rw [if_pos hn]
    have hy0 : y = [] := List.length_eq_zero_iff.1 hn
    subst hy0
    exact ⟨hx, by simp, hnx⟩
  rw [if_neg hn]
  rw [List.take_length]
  have hlen : (x.take y.length).length = y.length := by simp; omega
  obtain ⟨i1, i2, i3, i4⟩ := subVVc_spec (x.take y.length) y 0 (hx.take _) hy hlen.symm.symm (by omega)
  have hxs := take_len_drop_val x y.length hl
  have hlo : (subVV (x.take y.length) y).1.length = y.length := by unfold subVV; rw [i1, hlen]
  have hsum : val (subVV (x.take y.length) y).1 + val y = val (x.take y.length) + 2 ^ (64 * y.length) * (subVV (x.take y.length) y).2 := by
    unfold subVV; rw [hlen] at i4; omega
  have hc1 : (subVV (x.take y.length) y).2 ≤ 1 := i3
  have hwlo : Wd (subVV (x.take y.length) y).1 := i2
  generalize (subVV (x.take y.length) y).1 = lo at *
  generalize (subVV (x.take y.length) y).2 = c at *
  by_cases hgt : x.length > y.length
  · rw [if_pos hgt]
    have hxd : x.drop y.length ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    obtain ⟨j1, j2, j3, j4, j5⟩ := subVW_spec (x.drop y.length) c (hx.drop _) (by omega)
    generalize subVW (x.drop y.length) c = hh at *
    obtain ⟨hh1, hh2⟩ := hh
    have hl2 : (x.drop y.length).length = x.length - y.length := by simp
    simp only [hl2] at j1 j5
    simp only [] at j1 j2 j3 j4 j5 ⊢
    have hc2 := j3 hxd
    have hw : Wd (lo ++ hh1) := Wd_append.2 ⟨hwlo, j2⟩
    have hvl := val_lt hw
    rw [val_append] at hvl
    simp only [List.length_append, hlo, j1] at hvl
    have e2 : 2 ^ (64 * (y.length + (x.length - y.length))) = 2 ^ (64 * y.length) * 2 ^ (64 * (x.length - y.length)) := by
      rw [← Nat.pow_add, ← Nat.mul_add]
    rw [e2] at hvl
    have hxlen : y.length + (x.length - y.length) = x.length := by omega
    -- key identity
    have hP := congrArg (fun t => 2 ^ (64 * y.length) * t) j5
    simp only [Nat.mul_add] at hP
    have hid : val lo + 2 ^ (64 * y.length) * val hh1 + val y =
        val x + 2 ^ (64 * y.length) * 2 ^ (64 * (x.length - y.length)) * hh2 := by
      rw [hxs]
      have : 2 ^ (64 * y.length) * (2 ^ (64 * (x.length - y.length)) * hh2) =
          2 ^ (64 * y.length) * 2 ^ (64 * (x.length - y.length)) * hh2 := (Nat.mul_assoc _ _ _).symm
      omega
    have hh0 : hh2 = 0 := by
      rcases Nat.eq_zero_or_pos hh2 with h0 | h0
      · exact h0
      · have : 2 ^ (64 * y.length) * 2 ^ (64 * (x.length - y.length)) ≤
            2 ^ (64 * y.length) * 2 ^ (64 * (x.length - y.length)) * hh2 := Nat.le_mul_of_pos_right _ h0
        omega
    subst hh0
    refine ⟨Wd_norm hw, ?_, normed_norm _⟩
    rw [val_norm, val_append, hlo]
    omega
  · rw [if_neg hgt]
    have hxy : x.length = y.length := by omega
    have hxt : x.take y.length = x := by rw [← hxy]; exact List.take_length
    rw [hxt] at hsum
    have hvl := val_lt hwlo
    rw [hlo, ← hxy] at hvl
    have hc0 : c = 0 := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exact h0
      · have : 2 ^ (64 * x.length) ≤ 2 ^ (64 * x.length) * c := Nat.le_mul_of_pos_right _ h0
        rw [hxy] at this hvl
        omega
    subst hc0
    refine ⟨Wd_norm (by simpa using hwlo), ?_, normed_norm _⟩
    simp only [List.append_nil]
    rw [val_norm]
    omega

theorem natSub_spec (x y : List Nat) (hx : Wd x) (hy : Wd y) (hnx : Normed x) (hny : Normed y)
    (hle : val y ≤ val x) :
    Wd (natSub x y) ∧ val (natSub x y) = val x - val y ∧ Normed (natSub x y) := by
  unfold natSub
  by_cases h : x.length < y.length
  · -- impossible for normalised y: val y >= 2^(64*(|y|-1)) >= 2^(64|x|) > val x
    exfalso
    have hyne : y ≠ [] := by intro e; rw [e] at h; simp at h
    have h2 := hny.val_ge hyne hy
    have h1 := val_lt hx
    have : 2 ^ (64 * x.length) ≤ 2 ^ (64 * (y.length - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rw [if_neg h]
    exact natSubO_spec x y hx hy hnx (by omega) hle

/-! ## addTo -/

/-- nat.go:234 `addTo(z, x)`: z += x in place; `len(x) <= len(z)` is required (slice bounds), the carry out of `z` is dropped. -/
def addTo (z x : List Nat) : List Nat :=
  let n := x.length
  if n = 0 then z else
  let r := addVV (z.take n) (x.take n)
  if r.2 ≠ 0 ∧ n < z.length then r.1 ++ (addVW (z.drop n) r.2).1 else r.1 ++ z.drop n

theorem addTo_spec (z x : List Nat) (hz : Wd z) (hx : Wd x) (hl : x.length ≤ z.length)
    (hno : val z + val x < 2 ^ (64 * z.length)) :
    (addTo z x).length = z.length ∧ Wd (addTo z x) ∧ val (addTo z x) = val z + val x := by
  unfold addTo
  simp only []
  by_cases hn : x.length = 0
  · rw [if_pos hn]
    have : x = [] := List.length_eq_zero_iff.1 hn
    subst this
    exact ⟨rfl, hz, by simp⟩
  rw [if_neg hn]
  rw [List.take_length]
  have hlen : (z.take x.length).length = x.length := by simp; omega
  obtain ⟨i1, i2, i3, i4⟩ := addVVc_spec (z.take x.length) x 0 (hz.take _) hx hlen (by omega)
  have hzs := take_len_drop_val z x.length hl
  have hlo : (addVV (z.take x.length) x).1.length = x.length := by unfold addVV; rw [i1, hlen]
  have hsum : val (addVV (z.take x.length) x).1 + 2 ^ (64 * x.length) * (addVV (z.take x.length) x).2
      = val (z.take x.length) + val x := by
    unfold addVV; rw [hlen] at i4; omega
  have hwlo : Wd (addVV (z.take x.length) x).1 := i2
  have hc1' : (addVV (z.take x.length) x).2 ≤ 1 := i3
  have hdl : (z.drop x.length).length = z.length - x.length := by simp
  generalize (addVV (z.take x.length) x).1 = lo at *
  generalize (addVV (z.take x.length) x).2 = c at *
  have e2 : 2 ^ (64 * z.length) = 2 ^ (64 * x.length) * 2 ^ (64 * (z.length - x.length)) := by
    rw [← Nat.pow_add, ← Nat.mul_add]; congr 2; omega
  by_cases hc : c ≠ 0 ∧ x.length < z.length
  · rw [if_pos hc]
    have hzd : (z.drop x.length) ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    obtain ⟨j1, j2, j3, j4, j5⟩ := addVW_spec (z.drop x.length) c (hz.drop _) (by omega)
    have hw : Wd (lo ++ (addVW (z.drop x.length) c).1) := Wd_append.2 ⟨hwlo, j2⟩
    refine ⟨by rw [List.length_append, hlo, j1, hdl]; omega, hw, ?_⟩
    have hc1 := j3 hzd
    rw [hdl] at j1 j5
    rw [val_append, hlo]
    have hP := congrArg (fun t => 2 ^ (64 * x.length) * t) j5
    simp only [Nat.mul_add] at hP
    -- final carry must be 0
    have hc2 : (addVW (z.drop x.length) c).2 = 0 := by
      rcases Nat.eq_zero_or_pos (addVW (z.drop x.length) c).2 with h0 | h0
      · exact h0
      · have : 2 ^ (64 * x.length) * 2 ^ (64 * (z.length - x.length)) ≤
            2 ^ (64 * x.length) * (2 ^ (64 * (z.length - x.length)) * (addVW (z.drop x.length) c).2) := by
          rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ h0
        rw [e2] at hno
        omega
    rw [hc2] at hP
    simp only [Nat.mul_zero, Nat.add_zero] at hP
    omega
  · rw [if_neg hc]
    have hc0 : c = 0 := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exact h0
      · exfalso
        have hnz : x.length = z.length := by
          by_cases h : x.length < z.length
          · exact absurd ⟨by omega, h⟩ hc
          · omega
        have htk : z.take x.length = z := by rw [hnz]; exact List.take_length
        rw [htk] at hsum
        have h1 : 2 ^ (64 * x.length) ≤ 2 ^ (64 * x.length) * c := Nat.le_mul_of_pos_right _ h0
        rw [hnz] at h1 hsum
        omega
    subst hc0
    refine ⟨by simp [hlo, hdl]; omega, Wd_append.2 ⟨hwlo, hz.drop _⟩, ?_⟩
    rw [val_append, hlo]
    omega

/-! ## slices: take/drop values -/

theorem val_take_mod (x : List Nat) (k : Nat) (hx : Wd x) : val (x.take k) = val x % 2 ^ (64 * k) ∧
    val (x.drop k) = val x / 2 ^ (64 * k) := by
  by_cases h : k ≤ x.length
  · have hs := val_split x k h
    have hlt : val (x.take k) < 2 ^ (64 * k) := by
      have := val_lt (hx.take k)
      simpa [List.length_take, Nat.min_eq_left h] using this
    have hp := Nat.two_pow_pos (64 * k)
    constructor
    · rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · rw [hs, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · have h1 : x.take k = x := List.take_of_length_le (by omega)
    have h2 : x.drop k = [] := List.drop_of_length_le (by omega)
    have hlt : val x < 2 ^ (64 * k) :=
      Nat.lt_of_lt_of_le (val_lt hx) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [h1, h2, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]
    exact ⟨rfl, rfl⟩

/-! ## lsh / rsh / trunc -/

/-- nat.go:395 `(z nat) lsh(x nat, s uint) nat`.  `s = 0` returns `z` (`same`) or a copy of `x` (both = `x` for the value). -/
def natLsh (x : List Nat) (s : Nat) : List Nat :=
  if s = 0 then x else
  let m := x.length
  if m = 0 then [] else
  let n := m + s / 64
  let r := if s % 64 = 0 then (x, 0) else lshVU x (s % 64)     -- copy(z[n-m:n], x); z[n] = 0  |  z[n] = lshVU(z[n-m:n], x, s)
  norm (List.replicate (n - m) 0 ++ r.1 ++ [r.2])              -- clear(z[0:n-m]); z.norm()

theorem natLsh_spec (x : List Nat) (s : Nat) (hx : Wd x) (hnx : Normed x) :
    Wd (natLsh x s) ∧ val (natLsh x s) = val x * 2 ^ s ∧ Normed (natLsh x s) := by
  unfold natLsh
  by_cases hs : s = 0
  · rw [if_pos hs]; subst hs; exact ⟨hx, by simp, hnx⟩
  rw [if_neg hs]
  simp only []
  by_cases hm : x.length = 0
  · rw [if_pos hm]
    have : x = [] := List.length_eq_zero_iff.1 hm
    subst this
    exact ⟨Wd_nil, by simp, rfl⟩
  rw [if_neg hm]
  have hsplit : 2 ^ s = 2 ^ (64 * (s / 64)) * 2 ^ (s % 64) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hn : x.length + s / 64 - x.length = s / 64 := by omega
  rw [hn]
  by_cases hs64 : s % 64 = 0
  · rw [if_pos hs64]
    refine ⟨Wd_norm (Wd_append.2 ⟨Wd_append.2 ⟨Wd_replicate_zero _, hx⟩, by intro d hd; simp at hd; subst hd; decide⟩), ?_, normed_norm _⟩
    rw [val_norm, val_append, val_append, val_replicate_zero, List.length_append, List.length_replicate, hsplit, hs64]
    simp only [val_cons, val_nil, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.mul_comm]
  · rw [if_neg hs64]
    obtain ⟨i1, i2, i3, i4⟩ := lshVU_spec x (s % 64) hx (by omega) (by omega)
    generalize lshVU x (s % 64) = r at *
    obtain ⟨r1, r2⟩ := r
    simp only [] at i1 i2 i3 i4 ⊢
    refine ⟨Wd_norm (Wd_append.2 ⟨Wd_append.2 ⟨Wd_replicate_zero _, i2⟩, by intro d hd; simp at hd; subst hd; exact i3⟩), ?_, normed_norm _⟩
    rw [val_norm, val_append, val_append, val_replicate_zero, List.length_append, List.length_replicate, i1, hsplit]
    simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    have : 2 ^ (64 * (s / 64)) * (val r1 + 2 ^ (64 * x.length) * r2) = 2 ^ (64 * (s / 64)) * (val x * 2 ^ (s % 64)) := by rw [i4]
    rw [Nat.mul_add] at this
    have e : 2 ^ (64 * (s / 64)) * (val x * 2 ^ (s % 64)) = val x * (2 ^ (64 * (s / 64)) * 2 ^ (s % 64)) := by grind
    have e2 : 2 ^ (64 * (s / 64 + x.length)) = 2 ^ (64 * (s / 64)) * 2 ^ (64 * x.length) := by rw [Nat.mul_add, Nat.pow_add]
    have e3 : 2 ^ (64 * (s / 64)) * (2 ^ (64 * x.length) * r2) = 2 ^ (64 * (s / 64)) * 2 ^ (64 * x.length) * r2 := (Nat.mul_assoc _ _ _).symm
    rw [e2]
    omega

/-- nat.go:425 `(z nat) rsh(x nat, s uint) nat` (`s = 0`: `z` or a copy of `x`). -/
def natRsh (x : List Nat) (s : Nat) : List Nat :=
  if s = 0 then x else
  let m := x.length
  if m ≤ s / 64 then [] else                                   -- n := m - int(s/_W); if n <= 0 { return z[:0] }
  let xs := x.drop (s / 64)                                    -- x[m-n:]
  norm (if s % 64 = 0 then xs else (rshVU xs (s % 64)).1)      -- copy(z, x[m-n:]) | rshVU(z, x[m-n:], s)

theorem natRsh_spec (x : List Nat) (s : Nat) (hx : Wd x) (hnx : Normed x) :
    Wd (natRsh x s) ∧ val (natRsh x s) = val x / 2 ^ s ∧ Normed (natRsh x s) := by
  unfold natRsh
  by_cases hs : s = 0
  · rw [if_pos hs]; subst hs; exact ⟨hx, by simp, hnx⟩
  rw [if_neg hs]
  simp only []
  by_cases hm : x.length ≤ s / 64
  · rw [if_pos hm]
    refine ⟨Wd_nil, ?_, rfl⟩
    have hlt : val x < 2 ^ s := by
      refine Nat.lt_of_lt_of_le (val_lt hx) (Nat.pow_le_pow_right (by decide) ?_)
      omega
    rw [Nat.div_eq_of_lt hlt]; rfl
  rw [if_neg hm]
  have hd := (val_take_mod x (s / 64) hx).2
  have hwd := hx.drop (s / 64)
  have hsplit : 2 ^ s = 2 ^ (64 * (s / 64)) * 2 ^ (s % 64) := by
    rw [← Nat.pow_add]; congr 1; omega
  by_cases hs64 : s % 64 = 0
  · rw [if_pos hs64]
    refine ⟨Wd_norm hwd, ?_, normed_norm _⟩
    rw [val_norm, hd, hsplit, hs64]; simp
  · rw [if_neg hs64]
    have hne : x.drop (s / 64) ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    obtain ⟨i1, i2, i3, i4⟩ := rshVU_spec (x.drop (s / 64)) (s % 64) hwd (by omega) (by omega)
    refine ⟨Wd_norm i2, ?_, normed_norm _⟩
    rw [val_norm, i3, hd, Nat.div_div_eq_div_mul, ← hsplit]

/-- nat.go:530 `(z nat) trunc(x nat, n uint) nat`: x mod 2^n. -/
def natTrunc (x : List Nat) (n : Nat) : List Nat :=
  let w := (n + 63) / 64
  if x.length < w then x else
  let z := x.take w
  norm (if n % 64 ≠ 0 then upd z (w - 1) [z.getD (w - 1) 0 &&& (2 ^ (n % 64) - 1)] else z)

theorem natTrunc_spec (x : List Nat) (n : Nat) (hx : Wd x) (hnx : Normed x) :
    Wd (natTrunc x n) ∧ val (natTrunc x n) = val x % 2 ^ n ∧ Normed (natTrunc x n) := by
  unfold natTrunc
  simp only []
  by_cases hw : x.length < (n + 63) / 64
  · rw [if_pos hw]
    refine ⟨hx, ?_, hnx⟩
    have hlt : val x < 2 ^ n := by
      refine Nat.lt_of_lt_of_le (val_lt hx) (Nat.pow_le_pow_right (by decide) ?_)
      omega
    rw [Nat.mod_eq_of_lt hlt]
  rw [if_neg hw]
  have hxw : (n + 63) / 64 ≤ x.length := by omega
  by_cases hr : n % 64 ≠ 0
  · rw [if_pos hr]
    obtain ⟨k, hk⟩ : ∃ k, (n + 63) / 64 = k + 1 := ⟨(n + 63) / 64 - 1, by omega⟩
    rw [hk] at hxw ⊢
    have hkx : k < x.length := by omega
    have hnk : n = 64 * k + n % 64 := by omega
    have htk : x.take (k + 1) = x.take k ++ [x[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkx]; rfl
    have hdk : x.drop k = x[k] :: x.drop (k + 1) := List.drop_eq_getElem_cons hkx
    have hgetD : (x.take k ++ [x[k]]).getD (k + 1 - 1) 0 = x[k] := by
      have : (x.take k).length = k := by simp; omega
      simp only [Nat.add_sub_cancel]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [this]
    have hl1 : (x.take k).length = k := by simp; omega
    have hup : upd (x.take k ++ [x[k]]) (k + 1 - 1) [x[k] &&& (2 ^ (n % 64) - 1)] = x.take k ++ [x[k] % 2 ^ (n % 64)] := by
      unfold upd
      simp only [Nat.add_sub_cancel, Nat.and_two_pow_sub_one_eq_mod, List.length_singleton]
      rw [List.take_left' hl1, List.drop_of_length_le (by simp only [List.length_append, hl1, List.length_singleton]; omega)]
      simp
    rw [htk, hgetD, hup]
    have hr1 : 0 < n % 64 := by omega
    have hr2 : n % 64 < 64 := Nat.mod_lt _ (by omega)
    have hlt : x[k] % 2 ^ (n % 64) < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
    have hxk : x[k] < 2 ^ 64 := hx _ (List.getElem_mem hkx)
    refine ⟨Wd_norm (Wd_append.2 ⟨hx.take _, by intro d hd; simp at hd; subst hd; exact hlt⟩), ?_, normed_norm _⟩
    rw [val_norm, val_append, hl1]
    simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
    -- val x % 2^n
    have hs := val_split x k (by omega)
    have hT : val (x.take k) < 2 ^ (64 * k) := by
      have := val_lt (hx.take k)
      simpa [List.length_take, Nat.min_eq_left (show k ≤ x.length by omega)] using this
    have hU : val (x.drop k) = x[k] + 2 ^ (64 * 1) * val (x.drop (k + 1)) := by
      rw [hdk]; simp only [val_cons]
    have h2n : 2 ^ n = 2 ^ (64 * k) * 2 ^ (n % 64) := by
      rw [← Nat.pow_add]; congr 1
    have hq : 2 ^ 64 = 2 ^ (n % 64) * 2 ^ (64 - n % 64) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hUm : val (x.drop k) % 2 ^ (n % 64) = x[k] % 2 ^ (n % 64) := by
      rw [hU, Nat.mul_one, hq, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    generalize val (x.take k) = T at *
    generalize val (x.drop k) = U at *
    generalize 2 ^ (64 * k) = P at *
    have hqp : 0 < 2 ^ (n % 64) := Nat.two_pow_pos _
    generalize 2 ^ (n % 64) = q at *
    rw [h2n, hs]
    have e : T + P * U = (T + P * (U % q)) + (P * q) * (U / q) := by
      have := Nat.div_add_mod U q
      grind
    rw [e, Nat.add_mul_mod_self_left]
    have hb : U % q < q := Nat.mod_lt _ hqp
    have : T + P * (U % q) < P * q := by
      have : P * (U % q + 1) ≤ P * q := Nat.mul_le_mul_left _ hb
      rw [Nat.mul_add] at this; omega
    rw [Nat.mod_eq_of_lt this, hUm]
  · rw [if_neg hr]
    have hr0 : n % 64 = 0 := by omega
    have hw : (n + 63) / 64 = n / 64 := by omega
    rw [hw]
    have := (val_take_mod x (n / 64) hx).1
    refine ⟨Wd_norm (hx.take _), ?_, normed_norm _⟩
    rw [val_norm, this]
    congr 2; omega

end FvModexp.Mdl
