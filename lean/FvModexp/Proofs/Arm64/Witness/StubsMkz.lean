import FvModexp.Proofs.Arm64.Witness.Stubs

/-! # Witness stub: zero-byte `makeslice` (arm64)

The toy runtime's makeslice stub (`WStubs.mk`) satisfies the proposed zero-byte contract `MakesliceZeroLive`
(`Arm64/MakesliceZero.lean`): for `et.size · cap = 0` the block is `blockSize 0 _ = 0` bytes, so the stub's live-contract
post gives the invariant for `L ++ [(ptr, ptr)]` at budget `b - 0`; the toy invariant is monotone in the live set and
the empty range changes no byte of the view. -/

namespace FvModexp.Arm64.WStubs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

theorem inRs_snoc_empty (L : List (Nat × Nat)) (p a : Nat) : inRs (L ++ [(p, p)]) a = inRs L a := by
  simp only [inRs, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  have : (decide (p ≤ a) && decide (a < p)) = false := by
    by_cases h : p ≤ a <;> simp [h] <;> omega
  rw [this, Bool.or_false]

/-- Dropping an empty range from the live set keeps the toy invariant. -/
theorem toyInv_drop_empty {tys : Tys} {b g p : Nat} {L : List (Nat × Nat)} {m : Memory} (rt : List (Nat × Nat))
    (h : toyInv tys b (L ++ [(p, p)]) g (view rt (L ++ [(p, p)]) m)) : toyInv tys b L g (view rt L m) := by
  have hv : view rt (L ++ [(p, p)]) m = view rt L m := by
    simp only [view, inRs_snoc_empty]
  rw [hv] at h
  obtain ⟨q, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨q, h1, h2, h3, h4, fun r hr => h5 r (List.mem_append_left _ hr), h6⟩

theorem blockSize_zero' (b : Bool) : blockSize 0 b = 0 := by cases b <;> decide

/-- **The toy makeslice stub meets the zero-byte contract.** -/
theorem mkz (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MakesliceZeroLive P mkA 4096 (toyR tys ok) := by
  intro L b
  refine Summary.mono (mk tys hty ok L b) (fun s h => ?_) (fun s s' h hp => ?_)
  · obtain ⟨⟨hP, hR, hok, hinv, _, hs1, hs2⟩, hz⟩ := h
    have hr : makesliceRound s = 0 := by simp only [makesliceRound, hz, blockSize_zero']
    exact ⟨hP, hR, hok, hinv, by rw [hr]; exact Nat.zero_le _, hs1, hs2⟩
  · obtain ⟨_, hz⟩ := h
    have hr : makesliceRound s = 0 := by simp only [makesliceRound, hz, blockSize_zero']
    obtain ⟨ptr, junk, f, v, m, ex, ep, hs', hMF, hLF, _, _, hinv⟩ := hp
    rw [hr, Nat.sub_zero, Nat.add_zero] at hinv
    exact ⟨ptr, junk, f, v, m, ex, ep, hs', hMF, hLF, toyInv_drop_empty (g := (s.regs 28).toNat) _ hinv⟩

end FvModexp.Arm64.WStubs
