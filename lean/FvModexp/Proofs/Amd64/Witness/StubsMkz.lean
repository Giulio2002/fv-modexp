import FvModexp.Proofs.Amd64.Witness.Stubs

/-! # Witness stub: zero-byte `makeslice` (amd64)

The amd64 twin of `Arm64/Witness/StubsMkz.lean`: the toy runtime's makeslice stub (`WStubs.mk`) satisfies the zero-byte
contract `MakesliceZeroLive64` (`Amd64/MakesliceZero.lean`, = Janus PR #2's definition): for `et.size · cap = 0` the
block is `blockSize 0 _ = 0` bytes, so the live-contract post gives the toy invariant for `L ++ [(ptr, ptr)]` at budget
`b - 0`, and dropping the empty range keeps it (`toyInv_drop_empty`, as arm64). -/

namespace FvModexp.Amd64.WStubs

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

theorem inRs_snoc_empty (L : List (Nat × Nat)) (p a : Nat) : inRs (L ++ [(p, p)]) a = inRs L a := by
  simp only [inRs, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  have : (decide (p ≤ a) && decide (a < p)) = false := by
    by_cases h : p ≤ a <;> simp [h] <;> omega
  rw [this, Bool.or_false]

/-- Dropping an empty range from the live set keeps the toy invariant. -/
theorem toyInv_drop_empty {tys : Tys} {b g p : Nat} {L : List (Nat × Nat)} {m : Janus.Arm64.Memory}
    (rt : List (Nat × Nat)) (h : toyInv tys b (L ++ [(p, p)]) g (view rt (L ++ [(p, p)]) m)) :
    toyInv tys b L g (view rt L m) := by
  have hv : view rt (L ++ [(p, p)]) m = view rt L m := by
    simp only [view, inRs_snoc_empty]
  rw [hv] at h
  obtain ⟨q, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨q, h1, h2, h3, h4, fun r hr => h5 r (List.mem_append_left _ hr), h6⟩

theorem blockSize_zero' (b : Bool) : blockSize 0 b = 0 := by cases b <;> decide

/-- **The toy makeslice stub meets the zero-byte contract** (amd64). -/
theorem mkz (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MakesliceZeroLive64 P mkA 4096 (toyR tys ok) := by
  intro L b
  refine Janus.Amd64.Tactic.Summary.mono (mk tys hty ok L b) (fun s h => ?_) (fun s s' h hp => ?_)
  · obtain ⟨⟨hP, hR, hok, hinv, _, hs1, hs2⟩, hz, -⟩ := h
    have hr : makesliceRound64 s = 0 := by
      simp only [makesliceRound64, hz, blockSize_zero']
    exact ⟨hP, hR, hok, hinv, by rw [hr]; exact Nat.zero_le _, hs1, hs2⟩
  · obtain ⟨_, hz, -⟩ := h
    have hr : makesliceRound64 s = 0 := by
      simp only [makesliceRound64, hz, blockSize_zero']
    obtain ⟨ptr, junk, f, x, yh, m, zh, kr, hs', hMF, hLF, _, _, hinv⟩ := hp
    rw [hr, Nat.sub_zero, Nat.add_zero] at hinv
    exact ⟨ptr, junk, f, x, yh, m, zh, kr, hs', hMF, hLF,
      toyInv_drop_empty (g := (s.regs 14).toNat) _ hinv⟩

end FvModexp.Amd64.WStubs
