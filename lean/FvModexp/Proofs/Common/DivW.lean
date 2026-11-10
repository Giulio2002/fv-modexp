import FvModexp.Proofs.Common.DivWW
import FvModexp.Proofs.Common.NatBasic
/-!
# divWVW, divW (natdiv.go)

* `divWVW`   natdiv.go:579-591  `divWVW(z, xn, x, y)`: (xn:x) / y by word-wise 2-by-1 division with a reciprocal
* (`nat.divW`, natdiv.go:550-567, is modelled in NatDiv.lean)
-/
namespace FvModexp.Mdl

/-- The loop `for i := len(z)-1; i >= 0; i-- { z[i], r = divWW(r, x[i], y, rec) }`, on the most-significant-first list
(so the quotient digits come out most-significant first). -/
def divWVWLoop (y rec : Nat) : List Nat → Nat → List Nat × Nat
  | [], r => ([], r)
  | d :: ds, r =>
    let p := divWW r d y rec
    let t := divWVWLoop y rec ds p.2
    (p.1 :: t.1, t.2)

/-- `divWVW(z, xn, x, y)`: returns the new `z` (quotient digits, least significant first) and the remainder `r`. -/
def divWVW (xn : Nat) (x : List Nat) (y : Nat) : List Nat × Nat :=
  if x.length = 1 then
    let p := div64 xn (x.getD 0 0) y            -- qq, rr := bits.Div(uint(r), uint(x[0]), uint(y))
    ([p.1], p.2)
  else
    let t := divWVWLoop y (reciprocalWord y) x.reverse xn
    (t.1.reverse, t.2)

theorem divWVWLoop_spec (y : Nat) (hy : 0 < y) (hyB : y < 2 ^ 64) :
    ∀ (ds : List Nat) (r : Nat), Wd ds → r < y →
    (divWVWLoop y (reciprocalWord y) ds r).1.length = ds.length ∧ Wd (divWVWLoop y (reciprocalWord y) ds r).1 ∧
    (divWVWLoop y (reciprocalWord y) ds r).2 < y ∧
    r * 2 ^ (64 * ds.length) + msb 0 ds = y * msb 0 (divWVWLoop y (reciprocalWord y) ds r).1 + (divWVWLoop y (reciprocalWord y) ds r).2
  | [], r, _, hr => by simp [divWVWLoop, msb, hr, Wd_nil]
  | d :: ds, r, hds, hr => by
    have hd := Wd_cons.1 hds
    have hrec := reciprocalWord_spec y hy hyB
    have hspec := divWW_spec r d y (reciprocalWord y) hy hyB hr hd.1 hrec
    unfold divWVWLoop
    simp only []
    rw [hspec]
    simp only []
    have hrB : r < 2 ^ 64 := by omega
    have hq : (r * 2 ^ 64 + d) / y < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (r + 1) * 2 ^ 64 ≤ y * 2 ^ 64 := Nat.mul_le_mul_right _ hr
      rw [Nat.add_mul] at this
      rw [Nat.mul_comm y]; omega
    have hr' : (r * 2 ^ 64 + d) % y < y := Nat.mod_lt _ hy
    obtain ⟨i1, i2, i3, i4⟩ := divWVWLoop_spec y hy hyB ds ((r * 2 ^ 64 + d) % y) hd.2 hr'
    refine ⟨by simp [i1], Wd_cons.2 ⟨hq, i2⟩, i3, ?_⟩
    simp only [msb, Nat.zero_mul, Nat.zero_add] at *
    rw [msb_acc ds d, msb_acc (divWVWLoop y (reciprocalWord y) ds ((r * 2 ^ 64 + d) % y)).1 ((r * 2 ^ 64 + d) / y), i1]
    simp only [List.length_cons] at *
    rw [pow_succ64]
    have hdm := Nat.div_add_mod (r * 2 ^ 64 + d) y
    generalize (r * 2 ^ 64 + d) / y = q at *
    generalize (r * 2 ^ 64 + d) % y = r1 at *
    generalize msb 0 ds = D at *
    generalize msb 0 (divWVWLoop y (reciprocalWord y) ds r1).1 = Q at *
    generalize (divWVWLoop y (reciprocalWord y) ds r1).2 = R at *
    generalize 2 ^ (64 * ds.length) = P at *
    have := congrArg (fun t => t * P) hdm
    simp only [Nat.add_mul] at this
    grind

end FvModexp.Mdl
