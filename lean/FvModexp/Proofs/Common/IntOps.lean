import FvModexp.Proofs.Common.DivContract
/-!
# `big.Int` operations on `{neg, abs}` (int.go)

Go `Int{neg bool; abs nat}`.  `GInt.ival` is the integer it denotes.  A denormalised "-0" (`neg` with empty `abs`) is a legal
*input* (karatsubaSqr sets `z1.neg = true` before adding); results of the operations modelled here never are ("0 has no sign").

Pointer equality `x == y` (int.go:196 `Int.mul`, int.go:384 `Int.Cmp`) is a Bool parameter `same` with the hypothesis `same → y = x`.
Inputs: `GInt.Ok x` = `abs` is `Wd` and `Normed` (what `nat.add/sub/cmp` need).

* `intAdd`  int.go:141   `intSub` int.go:162   `intNeg` int.go:134   `intCmp` int.go:378
* `intMul`  int.go:191 (nat mul / sqr are parameters with `MulContract` / `SqrContract`)
* `intSign` int.go:44, `intSetInt64` int.go:58, `intSetUint64` int.go:70, `intSet` int.go:95
-/
namespace FvModexp.Mdl

structure GInt where
  neg : Bool
  abs : List Nat

/-- The integer denoted. -/
def GInt.ival (x : GInt) : Int := if x.neg then -((val x.abs : Nat) : Int) else ((val x.abs : Nat) : Int)

/-- Valid operand: `abs` is a normalised nat of words. -/
def GInt.Ok (x : GInt) : Prop := Wd x.abs ∧ Normed x.abs

/-- "0 has no sign": a negative Int has non-empty `abs`. -/
def GInt.Canon (x : GInt) : Prop := x.neg = true → x.abs ≠ []

/-- `z.neg = len(z.abs) > 0 && neg` (int.go:136,157,178,202). -/
def mkInt (neg : Bool) (abs : List Nat) : GInt := ⟨decide (abs ≠ []) && neg, abs⟩

theorem mkInt_canon (neg : Bool) (abs : List Nat) : (mkInt neg abs).Canon := by
  unfold mkInt GInt.Canon
  intro h; simp at h; exact h.1

theorem mkInt_abs (neg : Bool) (abs : List Nat) : (mkInt neg abs).abs = abs := rfl

theorem mkInt_ival (neg : Bool) (abs : List Nat) :
    (mkInt neg abs).ival = if neg then -((val abs : Nat) : Int) else ((val abs : Nat) : Int) := by
  unfold mkInt GInt.ival
  by_cases h : abs = []
  · subst h; cases neg <;> simp
  · cases neg <;> simp [h]

theorem normed_val_pos {l : List Nat} (hw : Wd l) (hn : Normed l) (hne : l ≠ []) : 0 < val l := by
  have := hn.val_ge hne hw
  have := Nat.two_pow_pos (64 * (l.length - 1))
  omega

/-! ## Neg / Sign / Set -/

/-- int.go:134 `Neg` (`z.Set(x)` then flip). -/
def intNeg (x : GInt) : GInt := mkInt (!x.neg) x.abs

theorem intNeg_spec (x : GInt) (hx : x.Ok) :
    (intNeg x).Ok ∧ (intNeg x).Canon ∧ (intNeg x).ival = -x.ival := by
  unfold intNeg
  refine ⟨hx, mkInt_canon _ _, ?_⟩
  rw [mkInt_ival]; unfold GInt.ival; cases x.neg <;> simp

/-- int.go:44 `Sign` (as an `Int` in {-1,0,1}). -/
def intSign (x : GInt) : Int := if x.abs.length = 0 then 0 else if x.neg then -1 else 1

theorem intSign_spec (x : GInt) (hx : x.Ok) (hc : x.Canon) :
    intSign x = if x.ival < 0 then -1 else if 0 < x.ival then 1 else 0 := by
  obtain ⟨hw, hn⟩ := hx
  unfold intSign GInt.ival
  by_cases h : x.abs = []
  · rw [h]; simp
  · have hlen : x.abs.length ≠ 0 := by simpa using h
    have hpos : 0 < val x.abs := normed_val_pos hw hn h
    rw [if_neg hlen]
    cases hneg : x.neg <;> simp [hneg] <;> omega

/-- int.go:95 `Set` (when `z != x`). -/
def intSet (x : GInt) : GInt := ⟨x.neg, x.abs⟩

theorem intSet_spec (x : GInt) : intSet x = x := rfl

/-- int.go:70 `SetUint64`. -/
def intSetUint64 (x : Nat) : GInt := ⟨false, natSetUint64 x⟩

theorem intSetUint64_spec (x : Nat) (h : x < 2 ^ 64) :
    (intSetUint64 x).Ok ∧ (intSetUint64 x).Canon ∧ (intSetUint64 x).ival = (x : Int) := by
  unfold intSetUint64
  rw [natSetUint64_spec x h]
  obtain ⟨a, b, c⟩ := natSetWord_spec x h
  refine ⟨⟨b, c⟩, by intro h; simp at h, ?_⟩
  unfold GInt.ival; simp [a]

/-- int.go:58 `SetInt64` for `|x| < 2^63` or `x = -2^63` (`uint64(-x)` wraps to `2^63`, which equals `natAbs`). -/
def intSetInt64 (x : Int) : GInt :=
  if x < 0 then ⟨true, natSetUint64 x.natAbs⟩ else ⟨false, natSetUint64 x.natAbs⟩

theorem intSetInt64_spec (x : Int) (h1 : -(2 ^ 63) ≤ x) (h2 : x < 2 ^ 63) :
    (intSetInt64 x).Ok ∧ (intSetInt64 x).Canon ∧ (intSetInt64 x).ival = x := by
  have hlt : x.natAbs < 2 ^ 64 := by omega
  obtain ⟨a, b, c⟩ := natSetWord_spec x.natAbs hlt
  unfold intSetInt64
  rw [natSetUint64_spec _ hlt]
  split
  · rename_i hn
    refine ⟨⟨b, c⟩, ?_, ?_⟩
    · intro _
      simp only []
      unfold natSetWord
      intro h; split at h
      · rename_i h0; omega
      · simp at h
    · unfold GInt.ival; simp only [if_true, a]; omega
  · rename_i hn
    refine ⟨⟨b, c⟩, by intro h; simp at h, ?_⟩
    unfold GInt.ival; simp only [a]; simp; omega

/-! ## Add / Sub -/

/-- int.go:141 `(z *Int) Add(x, y)`. -/
def intAdd (x y : GInt) : GInt :=
  if x.neg = y.neg then mkInt x.neg (natAdd x.abs y.abs)
  else if 0 ≤ natCmp x.abs y.abs then mkInt x.neg (natSub x.abs y.abs)
  else mkInt (!x.neg) (natSub y.abs x.abs)

/-- int.go:162 `(z *Int) Sub(x, y)`. -/
def intSub (x y : GInt) : GInt :=
  if x.neg ≠ y.neg then mkInt x.neg (natAdd x.abs y.abs)
  else if 0 ≤ natCmp x.abs y.abs then mkInt x.neg (natSub x.abs y.abs)
  else mkInt (!x.neg) (natSub y.abs x.abs)

theorem intAdd_spec (x y : GInt) (hx : x.Ok) (hy : y.Ok) :
    (intAdd x y).Ok ∧ (intAdd x y).Canon ∧ (intAdd x y).ival = x.ival + y.ival := by
  obtain ⟨hxw, hxn⟩ := hx
  obtain ⟨hyw, hyn⟩ := hy
  unfold intAdd
  by_cases hs : x.neg = y.neg
  · rw [if_pos hs]
    obtain ⟨a1, a2, a3⟩ := natAdd_spec x.abs y.abs hxw hyw hxn hyn
    refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_⟩
    rw [mkInt_ival, a2]; unfold GInt.ival; rw [← hs]; cases x.neg <;> simp <;> omega
  · rw [if_neg hs]
    have hc := natCmp_spec x.abs y.abs hxw hyw hxn hyn
    by_cases hge : 0 ≤ natCmp x.abs y.abs
    · rw [if_pos hge]
      rw [hc] at hge
      have hle : val y.abs ≤ val x.abs := by unfold cmpInt at hge; split at hge <;> (try split at hge) <;> omega
      obtain ⟨a1, a2, a3⟩ := natSub_spec x.abs y.abs hxw hyw hxn hyn hle
      refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_⟩
      rw [mkInt_ival, a2]; unfold GInt.ival
      cases hxn' : x.neg <;> cases hyn' : y.neg <;> simp_all <;> omega
    · rw [if_neg hge]
      rw [hc] at hge
      have hlt : val x.abs ≤ val y.abs := by unfold cmpInt at hge; split at hge <;> (try split at hge) <;> omega
      obtain ⟨a1, a2, a3⟩ := natSub_spec y.abs x.abs hyw hxw hyn hxn hlt
      refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_⟩
      rw [mkInt_ival, a2]; unfold GInt.ival
      cases hxn' : x.neg <;> cases hyn' : y.neg <;> simp_all <;> omega

theorem intSub_spec (x y : GInt) (hx : x.Ok) (hy : y.Ok) :
    (intSub x y).Ok ∧ (intSub x y).Canon ∧ (intSub x y).ival = x.ival - y.ival := by
  obtain ⟨hxw, hxn⟩ := hx
  obtain ⟨hyw, hyn⟩ := hy
  unfold intSub
  by_cases hs : x.neg ≠ y.neg
  · rw [if_pos hs]
    obtain ⟨a1, a2, a3⟩ := natAdd_spec x.abs y.abs hxw hyw hxn hyn
    refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_⟩
    rw [mkInt_ival, a2]; unfold GInt.ival
    cases hxn' : x.neg <;> cases hyn' : y.neg <;> simp_all <;> omega
  · rw [if_neg hs]
    have hs' : x.neg = y.neg := by simpa using hs
    have hc := natCmp_spec x.abs y.abs hxw hyw hxn hyn
    by_cases hge : 0 ≤ natCmp x.abs y.abs
    · rw [if_pos hge]
      rw [hc] at hge
      have hle : val y.abs ≤ val x.abs := by unfold cmpInt at hge; split at hge <;> (try split at hge) <;> omega
      obtain ⟨a1, a2, a3⟩ := natSub_spec x.abs y.abs hxw hyw hxn hyn hle
      refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_⟩
      rw [mkInt_ival, a2]; unfold GInt.ival
      cases hxn' : x.neg <;> simp_all <;> omega
    · rw [if_neg hge]
      rw [hc] at hge
      have hlt : val x.abs ≤ val y.abs := by unfold cmpInt at hge; split at hge <;> (try split at hge) <;> omega
      obtain ⟨a1, a2, a3⟩ := natSub_spec y.abs x.abs hyw hxw hyn hxn hlt
      refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_⟩
      rw [mkInt_ival, a2]; unfold GInt.ival
      cases hxn' : x.neg <;> simp_all <;> omega

/-! ## Cmp -/

/-- int.go:378 `(x *Int) Cmp(y)`; `same` is the pointer test `x == y`. -/
def intCmp (same : Bool) (x y : GInt) : Int :=
  if same then 0
  else if x.neg = y.neg then (if x.neg then -(natCmp x.abs y.abs) else natCmp x.abs y.abs)
  else if x.neg then -1 else 1

/-- For canonical operands (no "-0") `Cmp` is the three-way comparison of the values. -/
theorem intCmp_spec (same : Bool) (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hcx : x.Canon) (hcy : y.Canon)
    (hsame : same = true → y = x) :
    intCmp same x y = if x.ival < y.ival then -1 else if y.ival < x.ival then 1 else 0 := by
  obtain ⟨hxw, hxn⟩ := hx
  obtain ⟨hyw, hyn⟩ := hy
  unfold intCmp
  by_cases hs : same = true
  · rw [if_pos hs]; have := hsame hs; subst this; simp
  · rw [if_neg hs]
    have pos : ∀ z : GInt, z.Ok → z.Canon → z.neg = true → 0 < val z.abs :=
      fun z hz hc hn => normed_val_pos hz.1 hz.2 (hc hn)
    by_cases he : x.neg = y.neg
    · rw [if_pos he]
      have hc := natCmp_spec x.abs y.abs hxw hyw hxn hyn
      unfold GInt.ival
      rw [← he]
      cases x.neg
      · simp only [hc, cmpInt]; simp only [Bool.false_eq_true, if_false]
        split <;> split <;> omega
      · simp only [hc, cmpInt]; simp only [if_true]
        split <;> split <;> omega
    · rw [if_neg he]
      unfold GInt.ival
      cases hxn' : x.neg <;> cases hyn' : y.neg <;> simp_all
      · have := pos y ⟨hyw, hyn⟩ hcy hyn'; omega
      · have := pos x ⟨hxw, hxn⟩ hcx hxn'; omega

/-! ## Mul -/

/-- Contract of `(z nat) sqr(stk, x)` (natmul.go:73): normalised square, at most `2 len(x)` words. -/
def SqrContract (sqr : List Nat → List Nat) : Prop :=
  ∀ a : List Nat, Wd a →
    Wd (sqr a) ∧ val (sqr a) = val a * val a ∧ Normed (sqr a) ∧ (sqr a).length ≤ 2 * a.length

/-- int.go:191 `(z *Int) mul(stk, x, y)`; `same` is the pointer test `x == y` (int.go:196). -/
def intMul (nmul : List Nat → List Nat → List Nat) (nsqr : List Nat → List Nat) (same : Bool) (x y : GInt) : GInt :=
  if same then ⟨false, nsqr x.abs⟩
  else
    let a := nmul x.abs y.abs
    mkInt (x.neg != y.neg) a

theorem intMul_spec (nmul : List Nat → List Nat → List Nat) (nsqr : List Nat → List Nat)
    (hm : MulContract nmul) (hs : SqrContract nsqr) (same : Bool) (x y : GInt) (hx : x.Ok) (hy : y.Ok)
    (hsame : same = true → y = x) :
    (intMul nmul nsqr same x y).Ok ∧ (intMul nmul nsqr same x y).Canon ∧
    (intMul nmul nsqr same x y).ival = x.ival * y.ival ∧
    (same = true → (intMul nmul nsqr same x y).abs.length ≤ 2 * x.abs.length) ∧
    (same = false → (intMul nmul nsqr same x y).abs.length ≤ x.abs.length + y.abs.length) := by
  unfold intMul
  by_cases h : same = true
  · rw [if_pos h]
    have := hsame h; subst this
    obtain ⟨a1, a2, a3, a4⟩ := hs _ hx.1
    refine ⟨⟨a1, a3⟩, by intro h; simp at h, ?_, fun _ => a4, fun h' => by simp_all⟩
    unfold GInt.ival; simp only [Bool.false_eq_true, if_false]
    rw [a2]; cases GInt.neg _ <;> simp [Int.neg_mul_neg, Int.natCast_mul]
  · rw [if_neg h]
    simp only []
    obtain ⟨a1, a2, a3, a4⟩ := hm x.abs y.abs hx.1 hy.1
    refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_, fun h' => by simp_all, fun _ => a4⟩
    rw [mkInt_ival, a2]; unfold GInt.ival
    cases hxn : x.neg <;> cases hyn : y.neg <;> simp [Int.natCast_mul, Int.neg_mul, Int.mul_neg]

/-- `Int.mul` with `x != y` as pointers: only the nat multiplier is needed. -/
theorem intMul_ne_spec (nmul : List Nat → List Nat → List Nat) (nsqr : List Nat → List Nat)
    (x y : GInt) (hx : x.Ok) (hy : y.Ok)
    (hm : Wd x.abs → Wd y.abs → Wd (nmul x.abs y.abs) ∧ val (nmul x.abs y.abs) = val x.abs * val y.abs ∧
      Normed (nmul x.abs y.abs) ∧ (nmul x.abs y.abs).length ≤ x.abs.length + y.abs.length) :
    (intMul nmul nsqr false x y).Ok ∧ (intMul nmul nsqr false x y).Canon ∧
    (intMul nmul nsqr false x y).ival = x.ival * y.ival ∧
    (intMul nmul nsqr false x y).abs.length ≤ x.abs.length + y.abs.length := by
  unfold intMul
  simp only [Bool.false_eq_true, if_false]
  obtain ⟨a1, a2, a3, a4⟩ := hm hx.1 hy.1
  refine ⟨⟨a1, a3⟩, mkInt_canon _ _, ?_, a4⟩
  rw [mkInt_ival, a2]; unfold GInt.ival
  cases hxn : x.neg <;> cases hyn : y.neg <;> simp [Int.natCast_mul, Int.neg_mul, Int.mul_neg]

end FvModexp.Mdl
