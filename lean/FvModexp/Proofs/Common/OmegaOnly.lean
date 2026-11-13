import Lean

/-!
# `omega_only [h₁, …]`: `omega` on the listed hypotheses only (divmc s48, row-time trim)

Clears every other propositional hypothesis of the goal's context, then runs `omega`. Data variables stay (they
carry no facts). For side conditions such as `s.sp.toNat - 264 ≤ s.sp.toNat - 256` inside a large proof context, where
plain `omega` spends seconds on the unrelated (often disjunctive / truncated-subtraction) facts. Sound by
construction: clearing hypotheses only weakens the context; the proof term is the one `omega` builds.
-/

namespace FvModexp.Tactic

open Lean Elab Tactic Meta

syntax (name := omegaOnly) "omega_only" " [" term,* "]" : tactic

@[tactic omegaOnly] def evalOmegaOnly : Tactic := fun stx => do
  match stx with
  | `(tactic| omega_only [$hs,*]) =>
    let g ← getMainGoal
    let g' ← g.withContext do
      let mut keep : Array FVarId := #[]
      for h in hs.getElems do
        let e ← Term.elabTerm h none
        match e.fvarId? with
        | some f => keep := keep.push f
        | none => throwErrorAt h "omega_only: expected a local hypothesis"
      let mut toClear : Array FVarId := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        if keep.contains d.fvarId then continue
        unless ← isProp d.type do continue
        toClear := toClear.push d.fvarId
      g.tryClearMany toClear
    replaceMainGoal [g']
    evalTactic (← `(tactic| omega))
  | _ => throwUnsupportedSyntax

end FvModexp.Tactic
