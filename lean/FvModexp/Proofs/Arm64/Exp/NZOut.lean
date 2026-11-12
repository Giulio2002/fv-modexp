import FvModexp.Proofs.Arm64.Exp.NCallP

set_option autoImplicit false

/-!
# `nat.expNN` (arm64): the callee `z` argument is outside expNN's window — for every capacity (`ZArg.out`)

For infra's `ExpEven.Pre` conjunct `Outside zp (8 * zc) (win s stk above)` (NOTES-conventions "[infra s34]"), unguarded:
needed when `cap z = 0`. From `NPre`'s unguarded `Outside zp (8 * zc) [(sp - K, sp + 1432)]` (the entry `z`) and
`ZArg` (the argument is `nil`, the entry `z`, or a fresh runtime object).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

theorem ZArg.out {R : RtInv} {L : List (Nat × Nat)} {sp K zp zc zq zcq : Nat} (hza : ZArg R L sp K zp zc zq zcq)
    (hzo : Outside zp (8 * zc) [(sp - K, sp + 1432)]) (hwrt : Outside (sp - K) (K + 1432) R.rt) (hK : K ≤ sp) :
    Outside zq (8 * zcq) [(sp - K, sp + 1432)] := by
  rcases hza with ⟨e0, h | ⟨rfl, e1⟩⟩ | ⟨rfl, rfl, -⟩ | ⟨hin, -⟩
  · subst e0; subst h; simp only [outside_cons, outside_nil, and_true]; omega
  · subst e0; subst e1; exact hzo
  · exact hzo
  · have := out_inR2 hwrt hin
    simp only [outside_cons, outside_nil, and_true]; omega

end FvModexp.Arm64.ExpN
