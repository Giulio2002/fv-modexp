import FvModexp.Proofs.Arm64.Exp.NNilV

/-!
# `nat.expNN` (arm64), `stk == nil`: live-set lemmas for the deferred `Pool.Put`

After the `Put` the live set is `dropAll L2 rsF` (`rsF` = the stack's final ranges). `liveExt_dropAll`: when `L2`
extends `L1 = L ++ rs0` (the stack's initial ranges, fresh wrt `L`) and no range of `rsF` is in `L`, the result is
still a `LiveExt` of `L`. `held_dropAll`: a non-empty range held in `L2` and apart from every range of `rsF` is held
in `dropAll L2 rsF`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

theorem liveExt_dropAll {R : RtInv} {L L2 rs0 rsF : List (Nat × Nat)}
    (hrs0 : ∀ x ∈ rs0, InRanges x.1 (x.2 - x.1) R.rt ∧ ApartAll x.1 (x.2 - x.1) L)
    (hp0 : rs0.Pairwise fun a b => Apart a.1 (a.2 - a.1) b.1 (b.2 - b.1))
    (hx : LiveExt R (L ++ rs0) L2) (hF : ∀ r ∈ rsF, r ∉ L) : LiveExt R L (dropAll L2 rsF) := by
  obtain ⟨ns, rfl, hn1, hn2⟩ := hx
  refine ⟨dropAll (rs0 ++ ns) rsF, ?_, fun r hr => ?_, ?_⟩
  · simp only [dropAll, List.append_assoc, List.filter_append]
    congr 1
    rw [List.filter_eq_self]
    intro r hr
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun h => hF r h hr
  · rcases List.mem_append.1 (mem_dropAll hr) with h | h
    · exact hrs0 r h
    · obtain ⟨h1, h2⟩ := hn1 r h
      exact ⟨h1, fun q hq => h2 q (List.mem_append_left _ hq)⟩
  · refine List.Pairwise.sublist (List.filter_sublist) ?_
    rw [List.pairwise_append]
    exact ⟨hp0, hn2, fun a ha b hb => ((hn1 b hb).2 a (List.mem_append_right _ ha)).symm⟩

theorem held_dropAll {R : RtInv} {L rs : List (Nat × Nat)} {a n : Nat} (h : InRanges a n L ∨ Outside a n R.rt)
    (hn : 0 < n) (hap : ∀ r ∈ rs, Apart a n r.1 (r.2 - r.1)) : InRanges a n (dropAll L rs) ∨ Outside a n R.rt := by
  rcases h with ⟨q, hq, h1, h2⟩ | h
  · refine Or.inl ⟨q, mem_dropAll_of hq fun hm => ?_, h1, h2⟩
    have := hap q hm; unfold Apart at this; omega
  · exact Or.inr h

/-- every range of `stkRs` (header and, when `cap > 0`, the array) satisfies `P` when the header and the array do -/
theorem stkRs_forall {m : Memory} {d : Nat} {P : Nat × Nat → Prop} (hh : P (d, d + 24))
    (ha : 0 < stCap m d → P (stW m d, stW m d + 8 * stCap m d)) : ∀ r ∈ stkRs m d, P r := by
  intro r hr
  simp only [stkRs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact hh
  · split at hr
    · simp at hr
    · rename_i hc; simp only [List.mem_singleton] at hr; subst hr; exact ha (Nat.pos_of_ne_zero hc)

end FvModexp.Arm64.ExpN
