import FvModexp.Proofs.Amd64.Int.IntASDefs

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): the value of each path (pure; copy of the arm64 twin without its `TBZ` bit lemmas)

`nx, ny ∈ {0, 1}` the signs, `X, Y` the magnitudes. Path A (`nat.add`) is taken when the signs of `x` and `±y` agree
(`Add`: `nx = ny`; `Sub`: `nx ≠ ny`), else `x.abs.cmp(y.abs)` selects B (`X ≥ Y`: `X - Y`, sign `nx`) or C (`X < Y`:
`Y - X`, sign `!nx`). (amd64 tests `CMPB 0(CX), DL` on the sign bytes).
-/

open Janus Janus.Arm64

namespace FvModexp.Amd64.IntAS

/-- signed magnitude -/
@[reducible] def sgnZ (n v : Nat) : Int := if n = 0 then (v : Int) else -(v : Int)

theorem intZ_eq (m : Memory) (a : Nat) : intZ m a = sgnZ (hNeg m a) (natVal m (hP m a) (hL m a)) := rfl

theorem resA (sub : Bool) {nx ny X Y : Nat} (hnx : nx ≤ 1) (hny : ny ≤ 1) (hc : sub = true ↔ nx ≠ ny) :
    (if nx = 0 ∨ X + Y = 0 then ((X + Y : Nat) : Int) else -((X + Y : Nat) : Int)) =
      resZ sub (sgnZ nx X) (sgnZ ny Y) := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;>
    cases sub <;> simp at hc <;> by_cases h0 : X + Y = 0 <;> simp [resZ, sgnZ, h0] <;> omega

theorem resB (sub : Bool) {nx ny X Y : Nat} (hnx : nx ≤ 1) (hny : ny ≤ 1) (hc : sub = true ↔ nx = ny) (hYX : Y ≤ X) :
    (if nx = 0 ∨ X - Y = 0 then ((X - Y : Nat) : Int) else -((X - Y : Nat) : Int)) =
      resZ sub (sgnZ nx X) (sgnZ ny Y) := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;>
    cases sub <;> simp at hc <;> by_cases h0 : X - Y = 0 <;> simp [resZ, sgnZ, h0] <;> omega

theorem resC (sub : Bool) {nx ny X Y : Nat} (hnx : nx ≤ 1) (hny : ny ≤ 1) (hc : sub = true ↔ nx = ny) (hXY : X < Y) :
    (if 1 - nx = 0 ∨ Y - X = 0 then ((Y - X : Nat) : Int) else -((Y - X : Nat) : Int)) =
      resZ sub (sgnZ nx X) (sgnZ ny Y) := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;>
    cases sub <;> simp at hc <;> by_cases h0 : Y - X = 0 <;> simp [resZ, sgnZ, h0] <;> omega

end FvModexp.Amd64.IntAS
