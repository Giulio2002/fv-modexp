import Janus

/-!
# Frame helpers for the exponentiation-layer summaries (agent expmc)
-/

namespace FvModexp.Expmc

open Janus Janus.Arm64 Janus.Contracts

/-- A copy's destination reads as the source did. -/
theorem readLE_of_copied {m₀ m : Memory} {dst src n : Nat} (h : Mem.Copied m₀ m dst src n) :
    m.readLE dst n = m₀.readLE src n := by
  induction n generalizing dst src with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [Memory.readLE_succ, Memory.readLE_succ, h0]
    congr 2
    exact ih (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show dst + (i + 1) = dst + 1 + i by omega, show src + (i + 1) = src + 1 + i by omega] at this)

/-- An address in `rt` and outside `L` is outside every held range. -/
theorem outside_held {rt L : List (Nat × Nat)} {a : Nat} (h : (inRs rt a && !inRs L a) = true) :
    ∀ ws : List (Nat × Nat), (∀ r ∈ ws, InRanges r.1 (r.2 - r.1) L ∨ Outside r.1 (r.2 - r.1) rt) → Outside a 1 ws
  | [], _ => trivial
  | (lo, hi) :: ws, hws => by
    simp only [outside_cons]
    refine ⟨?_, outside_held h ws (fun r hr => hws r (List.mem_cons_of_mem _ hr))⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    refine Classical.byContradiction fun hc => ?_
    rcases hws (lo, hi) (List.mem_cons_self ..) with hL | hR
    · have := inRs_of_inRanges hL (x := a) (by simp only; omega) (by simp only; omega)
      rw [h.2] at this; cases this
    · have := inRs_of_outside hR (x := a) (by simp only; omega) (by simp only; omega)
      rw [h.1] at this; cases this

/-- The runtime invariant survives a frame whose written ranges are all held (in the live set or
outside the runtime-owned ranges). -/
theorem inv_frame {R : RtInv} {b g : Nat} {L ws : List (Nat × Nat)} {m m' : Memory} (hf : MemFrame m m' ws)
    (hws : ∀ r ∈ ws, InRanges r.1 (r.2 - r.1) L ∨ Outside r.1 (r.2 - r.1) R.rt)
    (h : R.inv b L g (view R.rt L m)) : R.inv b L g (view R.rt L m') := by
  refine R.ext b L g _ _ (fun a => ?_) (fun a n w => ?_) h
  · simp only [view]
    split
    · rename_i hx
      have := hf.readLE a 1 (outside_held hx ws hws)
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
    · rfl
  · simp only [view_accessible]; exact hf.accessible a n w

/-- The same for a single store into a held range. -/
theorem inv_writeLE {R : RtInv} {b g : Nat} {L : List (Nat × Nat)} {m : Memory} {a n v : Nat}
    (hh : InRanges a n L ∨ Outside a n R.rt) (h : R.inv b L g (view R.rt L m)) :
    R.inv b L g (view R.rt L (m.writeLE a n v)) := by
  rcases hh with hh | hh
  · rw [view_writeLE_live hh]; exact h
  · rw [view_writeLE_out hh]; exact h

/-- Widening a callee's two stack ranges into the caller's window. -/
theorem frame_widen2 {m m' : Memory} {rt : List (Nat × Nat)} {a1 b1 a2 b2 lo hi z1 z2 : Nat}
    (h : MemFrame m m' (rt ++ [(a1, b1), (a2, b2)] ++ [(z1, z2)])) (h1 : lo ≤ a1) (h2 : b1 ≤ hi) (h3 : lo ≤ a2)
    (h4 : b2 ≤ hi) : MemFrame m m' (rt ++ [(lo, hi), (z1, z2)]) :=
  h.mono fun a k hk => by
    simp only [outside_append, outside_cons, outside_nil, and_true] at hk ⊢
    obtain ⟨hrt, hw, hz⟩ := hk
    exact ⟨⟨hrt, by omega, by omega⟩, hz⟩

/-- A frame inside a window and a range, in the shape `rt ++ [window, range]`. -/
theorem frame_widen_rt {m m' : Memory} {rt ws : List (Nat × Nat)} (h : MemFrame m m' ws) :
    MemFrame m m' (rt ++ ws) :=
  h.mono fun a k hk => by simp only [outside_append] at hk; exact hk.2

end FvModexp.Expmc
