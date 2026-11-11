import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Common.DivmcMem

/-!
# `(*stack).nat` (amd64): the join after `slices.Grow` (`+0xdd`) and the pure postcondition

At `+0xdd` (`MOVQ DX, 0x8(AX)`) both paths (array kept, or `growslice` + `memclr`) have `AX = st`, `BX = n`,
`CX = c1` (the capacity), `DI = nr`, `DX = len`, `R8 = w1` (the array). `J` collects the facts there.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNat

/-- the join -/
abbrev pJ : Nat := segAddr Extracted.program fn + 0xdd
/-- `MOVQ R8, 0(AX)` (both write-barrier branches) -/
abbrev pS : Nat := segAddr Extracted.program fn + 0x101

@[reducible] def wJ (s : State) : List (Nat × Nat) := win s 4192 24

/-- The facts at the join (entry state `s`, memory `M`, live set `L1`, budget `b1`, array `(w1, c1)`). -/
structure J (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st n : Nat) (s : State)
    (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M : Memory) : Prop where
  pre : Pre R b L 4192 24 st n s
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  ra : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  mf : MemFrame s.mem M (R.rt ++ wJ s)
  lf : LiveFrame s.mem M L []
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) n ≤ b1
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M)
  wl : NatLive s.mem R L1 w1 c1
  c1len : stLen s.mem st + rnd n ≤ c1
  c1b : c1 < 2 ^ 40
  w64 : w1 < 2 ^ 64
  keep : stLen s.mem st + rnd n ≤ stCap s.mem st → w1 = stW s.mem st ∧ c1 = stCap s.mem st
  grow : stCap s.mem st < stLen s.mem st + rnd n → InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L
  lsep : LiveSep L1 (win s 4192 24)
  wwin : 0 < c1 → Outside w1 (8 * c1) (win s 4192 24)
  df0 : s.df = false

/-- the header is apart from the result's first word -/
theorem J.hdr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State} {L1 : List (Nat × Nat)}
    {b1 w1 c1 : Nat} {M : Memory} (h : J R b L st n s L1 b1 w1 c1 M) (hn : 0 < n) :
    Apart st 24 (w1 + 8 * stLen s.mem st) 8 := by
  have hpre := h.pre
  obtain ⟨-, -, hok, -, -, -, -, -, -, -, -, hfa⟩ := hpre
  obtain ⟨-, hsth, -, -, -, hlc, -⟩ := hok
  have hr4 : 4 ≤ rnd n := by simp only [rnd]; omega
  have hc1len := h.c1len
  by_cases hkp : stLen s.mem st + rnd n ≤ stCap s.mem st
  · obtain ⟨e1, -⟩ := h.keep hkp
    subst e1; unfold Apart at hfa ⊢; omega
  · obtain ⟨hin, hap⟩ := h.grow (by omega)
    have hin' : InRanges (w1 + 8 * stLen s.mem st) 8 R.rt := hin.sub (by omega) (by omega)
    rcases hsth with hL | hO
    · have := (ApartAll.sub' hap (a := w1 + 8 * stLen s.mem st) (n := 8) (by omega) (by omega)).apart_of_inRanges hL
      unfold Apart; omega
    · have := hin'.apart hO; unfold Apart at this ⊢; omega

/-- **The postcondition** from the memory `M3` at the return: header `(w1, len + nr, c1)`, the frame and live frame of
the whole call, the invariant. -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State} {L1 : List (Nat × Nat)}
    {b1 w1 c1 : Nat} {M : Memory} (h : J R b L st n s L1 b1 w1 c1 M) {M3 : Memory}
    (hacc : ∀ a k v, M3.accessible a k v = s.mem.accessible a k v)
    (hw : M3.readLE st 8 = w1) (hl : M3.readLE (st + 8) 8 = stLen s.mem st + rnd n) (hc : M3.readLE (st + 16) 8 = c1)
    (hF : MemFrame s.mem M3 (R.rt ++ win s 4192 24 ++ stkWs s.mem st))
    (hLF : LiveFrame s.mem M3 L (stkWs s.mem st))
    (hinv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M3)) :
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) n ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' M3)) ∧
      StkOK M3 R L' st ∧ stLen M3 st = stLen s.mem st + rnd n ∧
      (stLen s.mem st + rnd n ≤ stCap s.mem st → stW M3 st = stW s.mem st ∧ stCap M3 st = stCap s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → InRanges (stW M3 st) (8 * stCap M3 st) R.rt ∧
        ApartAll (stW M3 st) (8 * stCap M3 st) L) ∧
      MemFrame s.mem M3 (R.rt ++ win s 4192 24 ++ stkWs s.mem st) ∧ LiveFrame s.mem M3 L (stkWs s.mem st) := by
  obtain ⟨-, -, hok, -⟩ := h.pre
  obtain ⟨h8, hh, ha, h48, -, -, -⟩ := hok
  have e1 : stW M3 st = w1 := hw
  have e2 : stLen M3 st = stLen s.mem st + rnd n := hl
  have e3 : stCap M3 st = c1 := hc
  unfold StkOK
  rw [e1, e2, e3]
  refine ⟨L1, b1, ⟨h.ext, h.bud, hinv⟩, ⟨h8, h.ext.held hh, by rw [hacc]; exact ha, h48, ?_, ?_, h.c1b⟩, rfl, h.keep,
    h.grow, hF, hLF⟩
  · intro hc0
    obtain ⟨a1, a2, a3, a4⟩ := h.wl hc0
    exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · have := h.c1len; omega

/-- **The postcondition** after the stores of the tail: the memory `M2` at `+0xec` (header `len`/`cap` stored, the
write barrier's writes in `R.rt` and its stack), `M3` = `M2` with the header and the first word of the result
(`k = 1`, `n > 0`) written. -/
theorem post_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State} {L1 : List (Nat × Nat)}
    {b1 w1 c1 : Nat} {M : Memory} (h : J R b L st n s L1 b1 w1 c1 M) {M2 M3 : Memory}
    (hf : MemFrame M M2 (R.rt ++ [(st, st + 24), ((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)]))
    (hl : LiveFrame M M2 L1 [(st, st + 24)])
    (hinv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M2)) (k : Nat) (hk : k ≤ 1) (hkn : 0 < k → 0 < n)
    (hF3 : MemFrame M2 M3 ((st, st + 24) :: List.replicate k (w1 + 8 * stLen s.mem st, w1 + 8 * stLen s.mem st + 8)))
    (hw : M3.readLE st 8 = w1) (hl3 : M3.readLE (st + 8) 8 = stLen s.mem st + rnd n) (hc : M3.readLE (st + 16) 8 = c1) :
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) n ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' M3)) ∧
      StkOK M3 R L' st ∧ stLen M3 st = stLen s.mem st + rnd n ∧
      (stLen s.mem st + rnd n ≤ stCap s.mem st → stW M3 st = stW s.mem st ∧ stCap M3 st = stCap s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → InRanges (stW M3 st) (8 * stCap M3 st) R.rt ∧
        ApartAll (stW M3 st) (8 * stCap M3 st) L) ∧
      MemFrame s.mem M3 (R.rt ++ win s 4192 24 ++ stkWs s.mem st) ∧ LiveFrame s.mem M3 L (stkWs s.mem st) := by
  have hpre := h.pre
  obtain ⟨-, -, hok, hstw, harr, -, -, -, -, -⟩ := hpre
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  have hc1len := h.c1len
  have hr4 : 0 < n → 4 ≤ rnd n := fun hn => by simp only [rnd]; omega
  have hc0 : 0 < c1 ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · right; exact h0
    · left; have := hr4 (hkn h0); omega
  -- the result word: in the old free part (array kept) or in the fresh block
  have hx : (stW s.mem st + 8 * stLen s.mem st ≤ w1 + 8 * stLen s.mem st ∧
        w1 + 8 * stLen s.mem st + 8 * k ≤ stW s.mem st + 8 * stCap s.mem st) ∨
      (InRanges (w1 + 8 * stLen s.mem st) (8 * k) R.rt ∧ ApartAll (w1 + 8 * stLen s.mem st) (8 * k) L) := by
    by_cases hkp : stLen s.mem st + rnd n ≤ stCap s.mem st
    · obtain ⟨e1, e2⟩ := h.keep hkp
      left
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst e1; omega
      · have := hr4 (hkn h0); subst e1; omega
    · obtain ⟨hin, hap⟩ := h.grow (by omega)
      right
      have : stLen s.mem st + rnd n ≤ c1 := hc1len
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
      · have := hr4 (hkn h0)
        exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
  have hxh : k = 0 ∨ Held R L1 (w1 + 8 * stLen s.mem st) (8 * k) := by
    rcases hc0 with hc0 | h0
    · right
      obtain ⟨-, hh, -, -⟩ := h.wl hc0
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact hh.sub (by omega) (by omega)
      · have := hr4 (hkn h0); exact hh.sub (by omega) (by omega)
    · left; exact h0
  have hinv3 : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M3) := by
    refine RtInv.inv_frame' hF3 (fun r hr => ?_) hinv
    rcases List.mem_cons.1 hr with rfl | hr
    · simp only [show st + 24 - st = 24 by omega]
      exact (h.ext.held hsth).symm
    · obtain ⟨hk1, rfl⟩ := List.mem_replicate.1 hr
      simp only [show w1 + 8 * stLen s.mem st + 8 - (w1 + 8 * stLen s.mem st) = 8 * k by omega]
      rcases hxh with h0 | hh
      · omega
      · exact hh.symm
  have hF2 : MemFrame s.mem M2 (R.rt ++ win s 4192 24 ++ [(st, st + 24)]) := by
    refine h.mf.trans hf fun a n ho => ?_
    simp only [win, wJ, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, h1⟩, h3⟩ := ho
    exact ⟨⟨hrt, h1⟩, hrt, h3, by omega⟩
  refine post_of h (M3 := M3) (fun a n v => by rw [hF3.accessible, hF2.accessible]) hw hl3 hc ?_ ?_ hinv3
  · refine hF2.trans hF3 fun a n ho => ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, h1, h2⟩ := ho
    have hrep : Outside a n (List.replicate k (w1 + 8 * stLen s.mem st, w1 + 8 * stLen s.mem st + 8)) :=
      outside_of_forall fun r hr => by
        obtain ⟨hk1, rfl⟩ := List.mem_replicate.1 hr
        rcases hx with hx | ⟨hin, -⟩
        · simp only; omega
        · have := hin.apart hrt; unfold Apart at this; simp only; omega
    exact ⟨⟨⟨hrt, hw1⟩, h1⟩, h1, hrep⟩
  · refine ⟨fun a n hin hout => ?_⟩
    simp only [stkWs, outside_cons, outside_nil, and_true] at hout
    rw [hF3.readLE a n ?_, hl.readLE a n (h.ext.inRanges_old hin) ?_, h.lf.readLE a n hin trivial]
    · simp only [outside_cons, outside_nil, and_true]; exact hout.1
    · simp only [outside_cons]
      refine ⟨hout.1, outside_of_forall fun r hr => ?_⟩
      obtain ⟨hk1, rfl⟩ := List.mem_replicate.1 hr
      rcases hx with hx | ⟨-, hap⟩
      · simp only; omega
      · have := hap.apart_of_inRanges hin; simp only; omega

end FvModexp.Amd64.StackNat
