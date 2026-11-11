import FvModexp.Proofs.Arm64.Int.IntASDefs

/-!
# `(*Int).Add` / `(*Int).Sub` (arm64): the value of each path (pure)

`nx, ny ∈ {0, 1}` the signs, `X, Y` the magnitudes. Path A (`nat.add`) is taken when the signs of `x` and `±y` agree
(`Add`: `nx = ny`; `Sub`: `nx ≠ ny`), else `x.abs.cmp(y.abs)` selects B (`X ≥ Y`: `X - Y`, sign `nx`) or C (`X < Y`:
`Y - X`, sign `!nx`). Also: the bit the code tests (`TBZ/TBNZ $0` on `nx ^ ny`).
-/

open Janus Janus.Arm64

namespace FvModexp.Arm64.IntAS

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

/-- bit 0 of `nx ^ ny` (the code's first test) -/
theorem bit_xor {nx ny : Nat} (hnx : nx ≤ 1) (hny : ny ≤ 1) :
    ((BitVec.ofNat 64 nx ^^^ BitVec.ofNat 64 ny).getLsbD 0 == true) = decide (nx ≠ ny) := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;> decide

end FvModexp.Arm64.IntAS
