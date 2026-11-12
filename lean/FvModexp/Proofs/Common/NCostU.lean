/-!
# Monotone upper bounds of the expNN cost functions (agent expmc; [infra s38] ANSWER, coordinator 2026-11-14)

`ExpN.NCost costF costR costS costP x y a l k` and `NBudE … x y a l k` are NOT monotone in `a` (the window costs
contain `xl - n + 1`). `ExpEven.full`/`fullI` take dominating functions `bU`/`cU` with
`a ≤ a' → l ≤ l' → k ≤ k' → f x y a l k ≤ U x y a' l' k'`. `supU f` (the finite maximum of `f x y` over the box
`[0, a] × [0, l] × [0, k]`) is such a bound for EVERY `f` — no monotonicity premise on the callee costs — and is itself
monotone in `(a, l, k)`. Instantiate `bU := supU (NBudE costF costR costS costP)`,
`cU := supU (ExpN.NCost costF costR costS costP)`; `dom` gives `hNB`/`hNC`.
-/

set_option autoImplicit false

namespace FvModexp.Exp

/-- `max_{j ≤ n} f j` -/
def supN (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (supN f n) (f (n + 1))

theorem le_supN (f : Nat → Nat) : ∀ n j, j ≤ n → f j ≤ supN f n := by
  intro n
  induction n with
  | zero => intro j hj; rw [Nat.le_zero.1 hj]; exact Nat.le_refl _
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact Nat.le_trans (ih j (by omega)) (Nat.le_max_left _ _)
    · rw [show j = n + 1 by omega]; exact Nat.le_max_right _ _

theorem supN_mono (f : Nat → Nat) {n n' : Nat} (h : n ≤ n') : supN f n ≤ supN f n' := by
  induction n' with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ n' ih =>
    rcases Nat.lt_or_ge n (n' + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)
    · rw [show n = n' + 1 by omega]; exact Nat.le_refl _

theorem supN_le_of (f g : Nat → Nat) (h : ∀ j, f j ≤ g j) : ∀ n, supN f n ≤ supN g n := by
  intro n
  induction n with
  | zero => exact h 0
  | succ n ih => exact Nat.max_le.2 ⟨Nat.le_trans ih (Nat.le_max_left _ _), Nat.le_trans (h _) (Nat.le_max_right _ _)⟩

/-- the box maximum of `f x y · · ·` over `[0, a] × [0, l] × [0, k]` -/
def supU (f : Nat → Nat → Nat → Nat → Nat → Nat) (x y a l k : Nat) : Nat :=
  supN (fun a0 => supN (fun l0 => supN (fun k0 => f x y a0 l0 k0) k) l) a

/-- **domination**: `f x y a l k ≤ supU f x y a' l' k'` on the box -/
theorem dom (f : Nat → Nat → Nat → Nat → Nat → Nat) :
    ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' → f x y a l k ≤ supU f x y a' l' k' := by
  intro x y a a' l l' k k' ha hl hk
  unfold supU
  refine Nat.le_trans ?_ (le_supN _ a' a ha)
  refine Nat.le_trans ?_ (le_supN _ l' l hl)
  exact le_supN _ k' k hk

/-- `supU f` is monotone in `(a, l, k)` -/
theorem supU_mono (f : Nat → Nat → Nat → Nat → Nat → Nat) :
    ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' → supU f x y a l k ≤ supU f x y a' l' k' := by
  intro x y a a' l l' k k' ha hl hk
  unfold supU
  refine Nat.le_trans ?_ (supN_mono _ ha)
  refine supN_le_of _ _ (fun a0 => ?_) a
  refine Nat.le_trans ?_ (supN_mono _ hl)
  refine supN_le_of _ _ (fun l0 => ?_) l
  exact supN_mono _ hk

end FvModexp.Exp
