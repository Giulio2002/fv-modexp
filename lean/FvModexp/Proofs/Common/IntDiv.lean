import FvModexp.Proofs.Common.NatDiv
import FvModexp.Proofs.Common.IntOps
/-!
# `big.Int` division (int.go:299-340)

* `intQuoRem dr qs x y`  int.go:299 `QuoRem` (T-division): `(z, r)`; theorem `intQuoRem_spec`: `Int.tdiv`, `Int.tmod`
* `intDiv dr qs x y`     int.go:308 `Div` (Euclidean quotient);   theorem `intDiv_spec`: `x / y` (`Int.ediv`)
* `intMod dr qs x y`     int.go:325 `Mod` (Euclidean modulus);    theorem `intMod_spec`: `x % y` (`Int.emod`)

`dr` is the model of `divRecursive`, `qs` the quotient storage of `nat.div` (see NatDiv.lean).  `y ≠ 0` (`y.abs ≠ []`, the Go
division-by-zero panic) is a precondition.

**Aliasing.**  `Div`: `y_neg := y.neg` is saved before `QuoRem` because `z` may alias `y` (`z.neg` is overwritten).  `Mod`: `y0 := y`,
copied (`new(Int).Set(y)`) when `z == y` or `alias(z.abs, y.abs)` because `QuoRem` writes the remainder into `z`; the model
reads `y0` as the value `y` had before the call in both cases (`intSet`), so the one model covers aliased and non-aliased calls.
-/
namespace FvModexp.Mdl

/-- `intOne` (the Int constant 1). -/
def GInt.one : GInt := ⟨false, [1]⟩

theorem GInt.one_ok : GInt.one.Ok := ⟨by intro d hd; simp [GInt.one] at hd; subst hd; decide, by
  show norm [1] = [1]; simp [norm_cons]⟩

theorem GInt.one_ival : GInt.one.ival = 1 := by simp [GInt.one, GInt.ival, val]

/-- int.go:299 `(z *Int) QuoRem(x, y, r)`: `z.abs, r.abs = z.abs.div(nil, r.abs, x.abs, y.abs)`;
`z.neg = len(z.abs) > 0 && x.neg != y.neg`, `r.neg = len(r.abs) > 0 && x.neg`.  Returns `(z, r)`. -/
def intQuoRem (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (qs : List Nat) (x y : GInt) : GInt × GInt :=
  let p := natDiv dr qs x.abs y.abs
  (mkInt (x.neg != y.neg) p.1, mkInt x.neg p.2)

/-- Sign-magnitude integer. -/
def sgn (s : Bool) (n : Nat) : Int := if s then -(n : Int) else (n : Int)

theorem GInt.ival_eq (x : GInt) : x.ival = sgn x.neg (val x.abs) := rfl

theorem sgn_tdiv (sx sy : Bool) (X Y : Nat) :
    (sgn sx X).tdiv (sgn sy Y) = sgn (sx != sy) (X / Y) ∧ (sgn sx X).tmod (sgn sy Y) = sgn sx (X % Y) := by
  cases sx <;> cases sy <;> simp [sgn, Int.neg_tdiv, Int.tdiv_neg, Int.neg_tmod, Int.tmod_neg, ← Int.ofNat_tdiv, ← Int.ofNat_tmod]

theorem intQuoRem_spec (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (hdr : DivRecursiveContract dr)
    (qs : List Nat) (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hy0 : y.abs ≠ []) (hqs : Wd qs)
    (hqsl : 2 ≤ y.abs.length → y.abs.length ≤ x.abs.length → qs.length = x.abs.length - y.abs.length + 1) :
    (intQuoRem dr qs x y).1.Ok ∧ (intQuoRem dr qs x y).2.Ok ∧ (intQuoRem dr qs x y).1.Canon ∧ (intQuoRem dr qs x y).2.Canon ∧
    (intQuoRem dr qs x y).1.ival = x.ival.tdiv y.ival ∧ (intQuoRem dr qs x y).2.ival = x.ival.tmod y.ival := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := natDiv_spec dr hdr qs x.abs y.abs hx.1 hy.1 hx.2 hy.2 hy0 hqs hqsl
  unfold intQuoRem
  dsimp only
  refine ⟨⟨a1, a3⟩, ⟨a2, a4⟩, mkInt_canon _ _, mkInt_canon _ _, ?_, ?_⟩
  · rw [mkInt_ival, a5, GInt.ival_eq, GInt.ival_eq, (sgn_tdiv _ _ _ _).1]; rfl
  · rw [mkInt_ival, a6, GInt.ival_eq, GInt.ival_eq, (sgn_tdiv _ _ _ _).2]; rfl

/-- Euclidean from truncated division. -/
theorem eucl_from_trunc (a b : Int) (hb : b ≠ 0) :
    (0 ≤ a.tmod b → a / b = a.tdiv b ∧ a % b = a.tmod b) ∧
    (a.tmod b < 0 → 0 < b → a / b = a.tdiv b - 1 ∧ a % b = a.tmod b + b) ∧
    (a.tmod b < 0 → b < 0 → a / b = a.tdiv b + 1 ∧ a % b = a.tmod b - b) := by
  -- positive divisor
  have pos : ∀ (a b : Int), 0 < b →
      (0 ≤ a.tmod b → a / b = a.tdiv b ∧ a % b = a.tmod b) ∧
      (a.tmod b < 0 → a / b = a.tdiv b - 1 ∧ a % b = a.tmod b + b) := by
    intro a b hb
    have h1 := Int.mul_tdiv_add_tmod a b
    have h2 := Int.lt_tmod_of_pos a hb
    have h3 := Int.tmod_lt_of_pos a hb
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact (Int.ediv_emod_unique hb).2 ⟨by omega, h, h3⟩
    · have := (Int.ediv_emod_unique (a := a) (b := b) (r := a.tmod b + b) (q := a.tdiv b - 1) hb).2
        ⟨by rw [Int.mul_sub]; omega, by omega, by omega⟩
      exact this
  rcases Int.lt_or_gt_of_ne hb with hneg | hpos
  · -- b < 0 : reduce to -b
    have hb' : 0 < -b := by omega
    obtain ⟨p1, p2⟩ := pos a (-b) hb'
    have e1 : a / b = -(a / (-b)) := by
      have := Int.ediv_neg a (-b); rw [Int.neg_neg] at this; exact this
    have e2 : a % b = a % (-b) := by
      have := Int.emod_neg a (-b); rw [Int.neg_neg] at this; exact this
    have t1 : a.tdiv b = -(a.tdiv (-b)) := by
      have := Int.tdiv_neg a (-b); rw [Int.neg_neg] at this; exact this
    have t2 : a.tmod b = a.tmod (-b) := by
      have := Int.tmod_neg a (-b); rw [Int.neg_neg] at this; exact this
    rw [e1, e2, t1, t2]
    refine ⟨fun h => ?_, fun _ h => by omega, fun h _ => ?_⟩
    · have := p1 h; rw [this.1, this.2]; omega
    · have := p2 h; rw [this.1, this.2]; omega
  · obtain ⟨p1, p2⟩ := pos a b hpos
    exact ⟨p1, fun h _ => p2 h, fun h h' => by omega⟩

/-- `r.neg ↔ r < 0` for a canonical `Ok` Int. -/
theorem neg_iff_ival (r : GInt) (hr : r.Ok) (hc : r.Canon) : r.neg = true ↔ r.ival < 0 := by
  constructor
  · intro h
    have hne := hc h
    have := normed_val_pos hr.1 hr.2 hne
    unfold GInt.ival; rw [if_pos h]; omega
  · intro h
    cases hn : r.neg
    · unfold GInt.ival at h; rw [hn] at h; simp at h; omega
    · rfl

theorem GInt.ival_pos (y : GInt) (hy : y.Ok) (hy0 : y.abs ≠ []) : (y.neg = true → y.ival < 0) ∧ (y.neg = false → 0 < y.ival) := by
  have := normed_val_pos hy.1 hy.2 hy0
  unfold GInt.ival
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [h] <;> omega

/-- int.go:308 `(z *Int) Div(x, y)` (Euclidean quotient). -/
def intDiv (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (qs : List Nat) (x y : GInt) : GInt :=
  let y_neg := y.neg                                    -- y_neg := y.neg  (z may alias y)
  let zr := intQuoRem dr qs x y                         -- z.QuoRem(x, y, &r)
  if zr.2.neg then (if y_neg then intAdd zr.1 GInt.one else intSub zr.1 GInt.one) else zr.1

theorem intDiv_spec (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (hdr : DivRecursiveContract dr)
    (qs : List Nat) (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hy0 : y.abs ≠ []) (hqs : Wd qs)
    (hqsl : 2 ≤ y.abs.length → y.abs.length ≤ x.abs.length → qs.length = x.abs.length - y.abs.length + 1) :
    (intDiv dr qs x y).Ok ∧ (intDiv dr qs x y).Canon ∧ (intDiv dr qs x y).ival = x.ival / y.ival := by
  obtain ⟨q1, r1, q2, r2, q3, r3⟩ := intQuoRem_spec dr hdr qs x y hx hy hy0 hqs hqsl
  have hyne : y.ival ≠ 0 := by
    have := GInt.ival_pos y hy hy0
    cases h : y.neg
    · have := this.2 h; omega
    · have := this.1 h; omega
  obtain ⟨e1, e2, e3⟩ := eucl_from_trunc x.ival y.ival hyne
  have hneg := neg_iff_ival _ r1 r2
  have hyp := GInt.ival_pos y hy hy0
  unfold intDiv
  dsimp only
  generalize intQuoRem dr qs x y = zr at *
  by_cases hn : zr.2.neg = true
  · rw [if_pos hn]
    have hlt : zr.2.ival < 0 := hneg.1 hn
    rw [r3] at hlt
    by_cases hyn : y.neg = true
    · rw [if_pos hyn]
      obtain ⟨s1, s2, s3⟩ := intAdd_spec zr.1 GInt.one q1 GInt.one_ok
      refine ⟨s1, s2, ?_⟩
      rw [s3, GInt.one_ival, q3]
      have := e3 hlt (hyp.1 hyn); omega
    · have hyf : y.neg = false := by simpa using hyn
      rw [if_neg hyn]
      obtain ⟨s1, s2, s3⟩ := intSub_spec zr.1 GInt.one q1 GInt.one_ok
      refine ⟨s1, s2, ?_⟩
      rw [s3, GInt.one_ival, q3]
      have := e2 hlt (hyp.2 hyf); omega
  · rw [if_neg hn]
    have hge : 0 ≤ zr.2.ival := by
      refine Int.not_lt.1 (fun h => hn (hneg.2 h))
    rw [r3] at hge
    exact ⟨q1, q2, by rw [q3]; exact (e1 hge).1.symm⟩

/-- int.go:325 `(z *Int) Mod(x, y)` (Euclidean modulus). `QuoRem` is called on a temporary `q` with `z` as the remainder. -/
def intMod (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (qs : List Nat) (x y : GInt) : GInt :=
  let y0 := intSet y                                    -- y0 := y, or new(Int).Set(y) when z aliases y
  let z := (intQuoRem dr qs x y).2                      -- q.QuoRem(x, y, z)
  if z.neg then (if y0.neg then intSub z y0 else intAdd z y0) else z

theorem intMod_spec (dr : List Nat → List Nat → List Nat → List Nat × List Nat) (hdr : DivRecursiveContract dr)
    (qs : List Nat) (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hy0 : y.abs ≠ []) (hqs : Wd qs)
    (hqsl : 2 ≤ y.abs.length → y.abs.length ≤ x.abs.length → qs.length = x.abs.length - y.abs.length + 1) :
    (intMod dr qs x y).Ok ∧ (intMod dr qs x y).Canon ∧ (intMod dr qs x y).ival = x.ival % y.ival := by
  obtain ⟨q1, r1, q2, r2, q3, r3⟩ := intQuoRem_spec dr hdr qs x y hx hy hy0 hqs hqsl
  have hyne : y.ival ≠ 0 := by
    have := GInt.ival_pos y hy hy0
    cases h : y.neg
    · have := this.2 h; omega
    · have := this.1 h; omega
  obtain ⟨e1, e2, e3⟩ := eucl_from_trunc x.ival y.ival hyne
  have hneg := neg_iff_ival _ r1 r2
  have hyp := GInt.ival_pos y hy hy0
  unfold intMod
  dsimp only
  rw [intSet_spec]
  generalize intQuoRem dr qs x y = zr at *
  by_cases hn : zr.2.neg = true
  · rw [if_pos hn]
    have hlt : zr.2.ival < 0 := hneg.1 hn
    rw [r3] at hlt
    by_cases hyn : y.neg = true
    · rw [if_pos hyn]
      obtain ⟨s1, s2, s3⟩ := intSub_spec zr.2 y r1 hy
      refine ⟨s1, s2, ?_⟩
      rw [s3, r3]
      have := e3 hlt (hyp.1 hyn); omega
    · have hyf : y.neg = false := by simpa using hyn
      rw [if_neg hyn]
      obtain ⟨s1, s2, s3⟩ := intAdd_spec zr.2 y r1 hy
      refine ⟨s1, s2, ?_⟩
      rw [s3, r3]
      have := e2 hlt (hyp.2 hyf); omega
  · rw [if_neg hn]
    have hge : 0 ≤ zr.2.ival := by
      refine Int.not_lt.1 (fun h => hn (hneg.2 h))
    rw [r3] at hge
    exact ⟨r1, r2, by rw [r3]; exact (e1 hge).2.symm⟩

end FvModexp.Mdl
