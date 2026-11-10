import FvModexp.Proofs.Common.Conv

/-!
# Memory facts for composing the mul/div summaries (agent divmc; ISA independent)
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Contracts

/-- A live frame keeps the reads outside a smaller written set. -/
theorem LiveFrame.mono_ws {m m' : Memory} {L ws ws' : List (Nat × Nat)} (h : LiveFrame m m' L ws)
    (hs : ∀ a n, Outside a n ws' → Outside a n ws) : LiveFrame m m' L ws' :=
  ⟨fun a n hin ho => h.readLE a n hin (hs a n ho)⟩

/-- A held range outside what a summary wrote (`ws1` its stack window, `ws2` the caller-visible writes) keeps its
bytes. -/
theorem Held.readLE2 {R : RtInv} {L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (h : Held R L a n) (hf : MemFrame m m' (R.rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (ho1 : Outside a n ws1) (ho2 : Outside a n ws2) : m'.readLE a n = m.readLE a n := by
  rcases h with h | h
  · exact hl.readLE a n h ho2
  · exact hf.readLE a n (by simp only [Janus.outside_append]; exact ⟨⟨h, ho1⟩, ho2⟩)

/-- A live frame from a memory frame: the live set is outside the stack window `[lo, hi)` that holds every range of
`rs` (the function's own frame writes). -/
theorem liveFrame_of_frame {m m' : Memory} {L ws : List (Nat × Nat)} {rs : List (Nat × Nat)} {lo hi : Nat}
    (h : MemFrame m m' (rs ++ ws)) (hL : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ lo ∨ hi ≤ r.1)
    (hrs : ∀ r ∈ rs, lo ≤ r.1 ∧ r.2 ≤ hi) : LiveFrame m m' L ws :=
  ⟨fun a n hin hws => h.readLE a n (by
    rw [outside_append]
    refine ⟨outside_of_forall fun r hr => ?_, hws⟩
    obtain ⟨q, hq, h1, h2⟩ := hin
    have := hL q hq
    have := hrs r hr
    omega)⟩

/-- A read inside a zeroed range is `0`. -/
theorem readLE_of_zeroed {m : Memory} {a n : Nat} (h : Mem.Zeroed m a n) :
    ∀ k b, a ≤ b → b + k ≤ a + n → m.readLE b k = 0 := by
  intro k
  induction k with
  | zero => intro b _ _; rfl
  | succ k ih =>
    intro b h1 h2
    rw [Memory.readLE_succ, ih (b + 1) (by omega) (by omega)]
    have := h (b - a) (by omega)
    rw [show a + (b - a) = b by omega] at this
    rw [this]; rfl

end FvModexp
