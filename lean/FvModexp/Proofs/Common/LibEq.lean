/-!
# `List.filter` through a precomputed mask (agent expmc)

`eq_only` of a restricted-program constant with many names: `Program.onlySegments` filters the 84 Run segments by
`names.contains seg.name`; elaborator-side evaluation of the string comparisons times out for ~40 names. Instead the kernel
decides the mask `segments.map p = bs` (`decide +kernel`) and the filter is rewritten through the mask (`filter_mask`),
which reduces structurally (no strings).
-/

namespace FvModexp

/-- the filter through a mask of the predicate's values -/
def maskFilter {α : Type} : List α → List Bool → List α
  | a :: l, true :: bs => a :: maskFilter l bs
  | _ :: l, false :: bs => maskFilter l bs
  | _, _ => []

theorem filter_mask {α : Type} (p : α → Bool) : ∀ (l : List α) (bs : List Bool), l.map p = bs →
    l.filter p = maskFilter l bs
  | [], _, h => by subst h; rfl
  | a :: l, bs, h => by
    subst h
    cases ha : p a <;> simp only [List.map, List.filter, ha, maskFilter] <;> rw [filter_mask p l _ rfl]

end FvModexp
