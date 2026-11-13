import FvModexp.Proofs.Arm64.Nat.DrsRel

set_option autoImplicit false

/-!
# `divRecursiveStep` (arm64): sub-ranges of the written ranges `c.ws s` (speed helpers)

A callee's written range `[p, p + n)` inside `u`'s (or `z`'s) array is outside every range outside `c.ws s`. Stated
once here with a small context, so the call sites (`Mc.callN`/`McF.callN`/`Ev.callS` arguments) do not run `omega`
over the whole proof context (DrsC6: 19 s → < 1 s).
-/

open Janus Janus.Arm64

namespace FvModexp.Arm64.DivRec

theorem ws_up0 {c : Cx} {s : State} {x k p n : Nat} (h : Outside x k (c.ws s)) (h1 : c.up ≤ p)
    (h2 : p + n ≤ c.up + 8 * c.ul) : Outside x k [(p, p + n)] := by
  simp only [Cx.ws, outside_append, outside_cons] at h
  simp only [outside_cons, outside_nil, and_true]; omega

theorem ws_up {c : Cx} {s : State} {rs : List (Nat × Nat)} {x k p n : Nat} (h : Outside x k (rs ++ c.ws s))
    (h1 : c.up ≤ p) (h2 : p + n ≤ c.up + 8 * c.ul) : Outside x k [(p, p + n)] :=
  ws_up0 ((outside_append _ _ _ _).mp h).2 h1 h2

theorem ws_qp0 {c : Cx} {s : State} {x k p n : Nat} (h : Outside x k (c.ws s)) (h1 : c.qp ≤ p)
    (h2 : p + n ≤ c.qp + 8 * c.ql) : Outside x k [(p, p + n)] := by
  simp only [Cx.ws, outside_append, outside_cons] at h
  simp only [outside_cons, outside_nil, and_true]; omega

theorem ws_qp {c : Cx} {s : State} {rs : List (Nat × Nat)} {x k p n : Nat} (h : Outside x k (rs ++ c.ws s))
    (h1 : c.qp ≤ p) (h2 : p + n ≤ c.qp + 8 * c.ql) : Outside x k [(p, p + n)] :=
  ws_qp0 ((outside_append _ _ _ _).mp h).2 h1 h2

/-- `Asm.limbs` at equal arguments (instead of `congr 1`, which tries a slow defeq on the `Nat` arithmetic first) -/
theorem limbs_eq2 {m : Memory} {a a' n n' : Nat} (h1 : a = a') (h2 : n = n') : Asm.limbs m a n = Asm.limbs m a' n' := by
  subst h1; subst h2; rfl

end FvModexp.Arm64.DivRec
