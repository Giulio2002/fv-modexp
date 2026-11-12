import FvModexp.Proofs.Common.StackScr

/-!
# The `math/big.stackPool` object shape `StkSh` (ISA independent)

Coordinator decision on "[expmc s25] PROPOSAL" (NOTES-conventions): every `sync.(*Pool).Get` / `Put` premise of a row
(`getStack()` … deferred `stk.free()`) uses ONE pool shape, fixed by a row precondition (`Sh = StkSh`; Janus audit:
the shape is a runtime parameter):
* `SliceObj (2^40 - 1)` (Janus: a 24-byte header `{ptr, len, cap}` and, when `cap > 0`, its array, disjoint),
* `len = 0` (`free()` stores it before the `Put`; without it a `Get`'s `len` is unbounded),
* `cap = 0 → ptr = 0` (every stack user's precondition: an empty range inside a window is not `Outside`).

`stkRs m d`: the ranges `SliceObj` assigns to the header at `d` (header, and the array when `cap > 0`).
`StkSh.ok`: what a `Get` result gives a stack user (`StkOK`-style facts). `StkSh.of_ok`: re-establishing the shape at
the `Put` from the stack user's `StkOK` + `len = 0` + `cap = 0 → ptr = 0` (`ArrIn.cap0`) + header/array apartness.
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Spec Janus.Contracts Janus.Contracts.Pool

/-- the pooled `*big.stack` shape (see the module doc) -/
def StkSh : PoolShape := fun m d rs =>
  SliceObj (2 ^ 40 - 1) m d rs ∧ m.readLE (d + 8) 8 = 0 ∧ (m.readLE (d + 16) 8 = 0 → m.readLE d 8 = 0)

/-- the ranges `SliceObj` assigns to the header at `d` -/
@[reducible] def stkRs (m : Memory) (d : Nat) : List (Nat × Nat) :=
  (d, d + 24) :: (if stCap m d = 0 then [] else [(stW m d, stW m d + 8 * stCap m d)])

theorem StkSh.rs {m : Memory} {d : Nat} {rs : List (Nat × Nat)} (h : StkSh m d rs) : rs = stkRs m d := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, e⟩, -, -⟩ := h
  exact e

/-- the facts a `Get` result gives (`d` the header) -/
theorem StkSh.ok {m : Memory} {d : Nat} {rs : List (Nat × Nat)} (h : StkSh m d rs) :
    0 < d ∧ d % 8 = 0 ∧ d + 24 ≤ 2 ^ 48 ∧ m.accessible d 24 true = true ∧ stLen m d = 0 ∧ stCap m d < 2 ^ 40 ∧
      (stCap m d = 0 → stW m d = 0) ∧ stW m d % 8 = 0 ∧ stW m d + 8 * stCap m d ≤ 2 ^ 48 ∧
      (0 < stCap m d → m.accessible (stW m d) (8 * stCap m d) true = true) ∧
      Apart d 24 (stW m d) (8 * stCap m d) ∧ rs = stkRs m d := by
  obtain ⟨⟨h0, h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11⟩, hl, hc⟩ := h
  exact ⟨h0, h1, h2, h3, hl, by simp only [stCap]; omega, hc, h7, h8, h9, h10, h11⟩

/-- the shape from a stack user's facts (at the `Put`) -/
theorem StkSh.of_ok {m : Memory} {R : RtInv} {L : List (Nat × Nat)} {d : Nat} (hok : StkOK m R L d) (h0 : 0 < d)
    (hlen : stLen m d = 0) (hc0 : stCap m d = 0 → stW m d = 0)
    (hdis : 0 < stCap m d → Apart d 24 (stW m d) (8 * stCap m d)) : StkSh m d (stkRs m d) := by
  obtain ⟨h1, -, h3, h4, hnl, -, h7⟩ := hok
  refine ⟨⟨h0, h1, h4, h3, by simp only [stLen] at hlen ⊢; omega, by simp only [stCap] at h7 ⊢; omega,
    by decide, ?_, ?_, fun hc => (hnl hc).2.2.1, ?_, rfl⟩, hlen, hc0⟩
  · rcases Nat.eq_zero_or_pos (stCap m d) with hc | hc
    · have := hc0 hc; simp only [stW] at this ⊢; rw [this]
    · exact (hnl hc).1
  · rcases Nat.eq_zero_or_pos (stCap m d) with hc | hc
    · have := hc0 hc; simp only [stW, stCap] at this hc ⊢; rw [this, hc]; omega
    · exact (hnl hc).2.2.2
  · rcases Nat.eq_zero_or_pos (stCap m d) with hc | hc
    · have := hc0 hc; simp only [stW, stCap] at this hc ⊢; rw [this, hc]; unfold Disjoint; omega
    · have := hdis hc; unfold Apart at this; unfold Disjoint; simp only [stW, stCap] at this ⊢; omega

/-- every range of `stkRs` is non-empty -/
theorem stkRs_pos {m : Memory} {d : Nat} {r : Nat × Nat} (hr : r ∈ stkRs m d) : r.1 < r.2 := by
  simp only [stkRs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · simp only; omega
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr; simp only; omega

/-- a non-empty range apart from every element of `L` is not an element of `L` -/
theorem not_mem_of_apartAll {L : List (Nat × Nat)} {r : Nat × Nat} (hp : r.1 < r.2) (h : ApartAll r.1 (r.2 - r.1) L) :
    r ∉ L := by
  intro hm
  have := h r hm
  unfold Apart at this; omega

end FvModexp
