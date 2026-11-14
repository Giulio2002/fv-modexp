import FvModexp.Proofs.Common.NCostU

/-!
# `supU` in fold form, for row STATEMENTS (agent infra, s59)

`Exp.supN f` (structural recursion) mentions `f` twice in its compiled body (`f 0`, `f (n + 1)`), so the Janus
theorem audit, which expands every proof-local definition of a statement and then walks the result as a TREE
(JANUS-ISSUES "[infra s59] audit tree walk"), sees `supU f` (three nested `supN`) with ~8 copies of `f`: arm64
EvenRow's statement expanded to 36 M nodes and its audit ran > 13 min. `supNF`/`supUF` are the same functions
(`supNF_eq`, `supUF_eq`) with `f` mentioned ONCE (`List.range`/`List.foldl`/`max` are core, not expanded): the
statement expands to 2.3 M nodes. Rows state their bounds with `supUF` and use `domF`.
-/

set_option autoImplicit false

namespace FvModexp.Exp

/-- `max_{j ≤ n} f j` as a fold (`= supN f n`, `supNF_eq`) -/
def supNF (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun m i => max m (f i)) 0

theorem supNF_eq (f : Nat → Nat) : ∀ n, supNF f n = supN f n := by
  intro n
  induction n with
  | zero => simp [supNF, supN, List.range_succ]
  | succ n ih =>
    simp only [supNF] at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    rfl

/-- the box maximum (`= supU f`, `supUF_eq`) with `f` mentioned once -/
def supUF (f : Nat → Nat → Nat → Nat → Nat → Nat) (x y a l k : Nat) : Nat :=
  supNF (fun a0 => supNF (fun l0 => supNF (fun k0 => f x y a0 l0 k0) k) l) a

theorem supUF_eq (f : Nat → Nat → Nat → Nat → Nat → Nat) : supUF f = supU f := by
  funext x y a l k
  simp only [supUF, supU, supNF_eq]

/-- **domination** for `supUF` (= `dom`) -/
theorem domF (f : Nat → Nat → Nat → Nat → Nat → Nat) :
    ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' → f x y a l k ≤ supUF f x y a' l' k' := by
  rw [supUF_eq]; exact dom f

end FvModexp.Exp
