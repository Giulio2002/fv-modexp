import Janus

/-!
# `gen_reg`: name a register value of a symbolic state

`gen_reg r as x with h` finds the outermost `setReg _ r v` (arm64 `Janus.Tactic.setReg`, amd64 `Janus.Amd64.Tactic.setRegF`) in
the goal and generalizes `v` to a fresh variable `x` with `h : v = x` (Lean's `generalize`). Used after a `janus_run` to
stop a large register term (e.g. `nat.bitLen`'s bit smear and `CLZ`) from being re-simplified by every later step and
from being copied into `CSEL` conditions. Pure tactic: it only calls `MVarId.generalize`, the kernel checks the result.
-/

namespace FvModexp.Tac

open Lean Elab Tactic Meta

private def isSetRegAt (k : Nat) (e : Expr) : Bool :=
  (e.isAppOfArity ``Janus.Tactic.setReg 3 || e.isAppOfArity ``Janus.Amd64.Tactic.setRegF 3) &&
    ((e.getArg! 1).nat?.map (· == k)).getD false

elab "gen_reg " r:num " as " x:ident " with " h:ident : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let k := r.getNat
  let some e := goal.find? (isSetRegAt k)
    | throwError "gen_reg: no `setReg _ {k} _` in the goal"
  let v := e.getArg! 2
  let (_, mv') ← (← getMainGoal).generalize #[{ expr := v, xName? := x.getId, hName? := h.getId }]
  replaceMainGoal [mv']

end FvModexp.Tac
