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

theorem liveFrame_widen {m m' : Memory} {L ws ws' : List (Nat × Nat)} (h : LiveFrame m m' L ws)
    (sub : ∀ a k, Outside a k ws' → Outside a k ws) : LiveFrame m m' L ws' :=
  ⟨fun a k hin hout => h.readLE a k hin (sub a k hout)⟩

theorem liveFrame_of_frame {m m' : Memory} {L ws rs : List (Nat × Nat)} (h : MemFrame m m' rs)
    (ho : ∀ a k, InRanges a k L → Outside a k ws → Outside a k rs) : LiveFrame m m' L ws :=
  ⟨fun a k hin hout => h.readLE a k (ho a k hin hout)⟩

/-- A held range outside the extra written ranges keeps its bytes through a live call (`MemFrame` over
`rt ++ ws1 ++ ws2`, `LiveFrame` exempting `ws2`). -/
theorem held_readLE {rt L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (hh : InRanges a n L ∨ Outside a n rt) (hf : MemFrame m m' (rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (h1 : Outside a n ws1) (h2 : Outside a n ws2) : m'.readLE a n = m.readLE a n := by
  rcases hh with hh | hh
  · exact hl.readLE a n hh h2
  · exact hf.readLE a n (by simp only [outside_append]; exact ⟨⟨hh, h1⟩, h2⟩)

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- A read through a live call's frame at a stack slot (inside a window outside `rt`). -/
theorem slot_read {rt cs z : List (Nat × Nat)} {base w : Memory} (F : MemFrame base w (rt ++ cs ++ z))
    {lo len a k : Nat} (hwin : Outside lo len rt) (h1 : lo ≤ a) (h2 : a + k ≤ lo + len)
    (hcs : Outside a k cs) (hz : Outside a k z) : w.readLE a k = base.readLE a k :=
  F.readLE a k (by simp only [outside_append]; exact ⟨⟨hwin.of_sub h1 h2, hcs⟩, hz⟩)

theorem readLE_writeLE_same {m : Memory} {a b k v : Nat} (h : a = b) : (m.writeLE a k v).readLE b k = v % 256 ^ k := by
  subst h; exact Memory.readLE_writeLE_self _ _ _ _

theorem readLE_zeroed {m : Memory} {a n : Nat} (h : Mem.Zeroed m a n) : m.readLE a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Memory.readLE_succ, ih (fun i hi => by
      have := h (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega] at this)]
    have := h 0 (by omega); rw [Nat.add_zero] at this; rw [this]; rfl

theorem sp_sub (x : BitVec 64) (k : Nat) (hk : k ≤ x.toNat) (hk' : k < 2 ^ 64) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- The frame facts of an exit path whose stores lie in the window and in `z[:n]`. -/
theorem close_frame {R : RtInv} {L : List (Nat × Nat)} {b g lo hi zp n : Nat} {M w : Memory}
    (hF : MemFrame M w [(lo, hi), (zp, zp + 8 * n)]) (hwin : Outside lo (hi - lo) R.rt)
    (hzh : InRanges zp (8 * n) L ∨ Outside zp (8 * n) R.rt) (hLs : LiveSep L [(lo, hi)])
    (hinv : R.inv b L g (view R.rt L M)) :
    R.inv b L g (view R.rt L w) ∧ MemFrame M w (R.rt ++ [(lo, hi), (zp, zp + 8 * n)]) ∧
      LiveFrame M w L [(zp, zp + 8 * n)] := by
  refine ⟨inv_frame hF (fun r hr => ?_) hinv, frame_widen_rt hF, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr hwin
    · simpa using hzh
  · refine ⟨fun a k hin hout => hF.readLE a k ?_⟩
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this hout ⊢
    omega

/-- Widening a callee's two stack ranges and its destination into the caller's window and range. -/
theorem frame_widen2' {m m' : Memory} {rt : List (Nat × Nat)} {a1 b1 a2 b2 lo hi z1 z2 y1 y2 : Nat}
    (h : MemFrame m m' (rt ++ [(a1, b1), (a2, b2)] ++ [(z1, z2)])) (h1 : lo ≤ a1) (h2 : b1 ≤ hi) (h3 : lo ≤ a2)
    (h4 : b2 ≤ hi) (h5 : y1 ≤ z1) (h6 : z2 ≤ y2) : MemFrame m m' (rt ++ [(lo, hi), (y1, y2)]) :=
  h.mono fun a k hk => by
    simp only [outside_append, outside_cons, outside_nil, and_true] at hk ⊢
    obtain ⟨hrt, hw, hz⟩ := hk
    exact ⟨⟨hrt, by omega, by omega⟩, by omega⟩

/-- A range inside a window that no live object meets is outside the live set. -/
theorem outside_of_liveSep {L : List (Nat × Nat)} {lo hi a k : Nat} (hLs : LiveSep L [(lo, hi)]) (h1 : lo ≤ a)
    (h2 : a + k ≤ hi) : Outside a k L := by
  induction L with
  | nil => trivial
  | cons r L ih =>
    obtain ⟨r1, r2⟩ := r
    have := hLs (r1, r2) (List.mem_cons_self ..)
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    exact ⟨by omega, ih (fun r hr => hLs r (List.mem_cons_of_mem _ hr))⟩

end FvModexp.Expmc
