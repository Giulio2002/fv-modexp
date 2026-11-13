import FvModexp.Proofs.Arm64.Conv

set_option autoImplicit false

/-!
# A callee window inside the caller's window (arm64; speed helper)

`winA_in`: a range outside the caller's window `winA s W 96` is outside the window `winA X stk ab` of a callee whose
`SP` is `d` bytes lower (`stk + d ≤ W`, `ab + 8 ≤ d`). Stated once with a small context: the `hS` facts of the drs /
divLarge call sites ran `omega` over the whole proof context (DrsMulQ: 77 s).
-/

open Janus Janus.Arm64

namespace FvModexp.Arm64

theorem winA_in {s X : State} {x k W d stk ab : Nat} (ho : Outside x k (winA s W 96))
    (hsp : X.sp.toNat = s.sp.toNat - d) (hd : d ≤ s.sp.toNat) (h1 : stk + d ≤ W) (h2 : ab + 8 ≤ d) :
    Outside x k (winA X stk ab) := by
  simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hsp]; omega

/-- a smaller window at the same `SP` -/
theorem winA_mono {s : State} {x k W a stk ab : Nat} (ho : Outside x k (winA s W a)) (h1 : stk ≤ W) (h2 : ab ≤ a) :
    Outside x k (winA s stk ab) := by
  simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; omega

end FvModexp.Arm64
