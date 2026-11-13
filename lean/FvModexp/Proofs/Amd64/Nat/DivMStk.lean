import FvModexp.Proofs.Common.StkPool

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`: the new stack `NewStk` and the live-set lemmas of the deferred `Pool.Put`

Copied (ISA-independent statements, unchanged proofs) from agent expmc's `nat.expNN` `stk == nil` modules, so that
`nat.div`'s chain does not import the `expNN` closure: `NewStk` (Arm64/Exp/NNilD.lean), `NewStk.hdr/arr/mem/held/apart/
out/liveSep` (NNilV), `NewStk.outWs/outL`, `stkOK_frame`, `stkRs_congr`, `liveSep_ext` (NNilKP), `liveExt_dropAll`,
`held_dropAll`, `stkRs_forall` (NNilP), `outside_of_rt`, `newStk_T` (NNilG), `out_inR2`, `apart_fresh` (NPost), `freeR` (= `W4En.free`), `outside_of_forall`
(P2PreKeep). Namespace `FvModexp.Amd64.DivNil`. (amd64 copy of Arm64/Nat/DivMStk.lean, top s40: the statements and proofs are
ISA independent (`Janus.Arm64.Memory` is both ISAs' memory); importing only Common/StkPool.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

namespace FvModexp.Amd64.DivNil

/-- the new stack `st` (from `Get` or `newobject`) at memory `M1`: its ranges `stkRs M1 st` are fresh runtime
objects added to the live set (`L1 = L ++ stkRs M1 st`), it is empty (`len = 0`), of the pool shape; budget at most
the 24 bytes of `newobject` less -/
def NewStk (R : RtInv) (L L1 : List (Nat × Nat)) (b b1 : Nat) (g : Nat) (M1 : Memory) (st : Nat) : Prop :=
  L1 = L ++ stkRs M1 st ∧ (∀ x ∈ stkRs M1 st, InRanges x.1 (x.2 - x.1) R.rt ∧ ApartAll x.1 (x.2 - x.1) L) ∧
  0 < st ∧ st % 8 = 0 ∧ st + 24 ≤ 2 ^ 48 ∧ M1.accessible st 24 true = true ∧ stLen M1 st = 0 ∧
  stCap M1 st < 2 ^ 40 ∧ (stCap M1 st = 0 → stW M1 st = 0) ∧ stW M1 st % 8 = 0 ∧
  stW M1 st + 8 * stCap M1 st ≤ 2 ^ 48 ∧
  (0 < stCap M1 st → M1.accessible (stW M1 st) (8 * stCap M1 st) true = true) ∧
  Apart st 24 (stW M1 st) (8 * stCap M1 st) ∧ b ≤ b1 + 24 ∧ b1 ≤ b ∧
  R.inv b1 L1 g (view R.rt L1 M1)


theorem out_inR2 {a n p k : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hin : InRanges p k rs) :
    a + n ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem h hr
  omega


theorem apart_fresh {R : RtInv} {L : List (Nat × Nat)} {a n p r : Nat} (hH : InRanges a n L ∨ Outside a n R.rt)
    (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) : a + n ≤ p ∨ p + r ≤ a := by
  rcases hH with ⟨q, hq, h1, h2⟩ | ho
  · have := hAp q hq; unfold Apart at this; omega
  · exact out_inR2 ho hIn

/-- the free part of a stack (agent expmc's `W4En.free`) -/
@[reducible] def freeR (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

theorem outside_of_forall {b k : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, b + k ≤ r.1 ∨ r.2 ≤ b) → Outside b k rs
  | [], _ => trivial
  | (lo, hi) :: rs, h => ⟨h (lo, hi) List.mem_cons_self, outside_of_forall fun r hr => h r (List.mem_cons_of_mem _ hr)⟩


section
variable {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {M1 : Memory} {st : Nat}

theorem NewStk.hdr (hN : NewStk R L L1 b b1 g M1 st) : InRanges st 24 R.rt ∧ ApartAll st 24 L := by
  have h := hN.2.1 (st, st + 24) (List.mem_cons_self ..)
  simpa only [Nat.add_sub_cancel_left] using h

theorem NewStk.arr (hN : NewStk R L L1 b b1 g M1 st) (hc : 0 < stCap M1 st) :
    InRanges (stW M1 st) (8 * stCap M1 st) R.rt ∧ ApartAll (stW M1 st) (8 * stCap M1 st) L := by
  have hm : (stW M1 st, stW M1 st + 8 * stCap M1 st) ∈ stkRs M1 st := by
    simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, List.mem_singleton, true_or, or_true]
  have h := hN.2.1 _ hm
  simpa only [Nat.add_sub_cancel_left] using h

theorem NewStk.mem (hN : NewStk R L L1 b b1 g M1 st) {r : Nat × Nat} (hr : r ∈ L) : r ∈ L1 := by
  rw [hN.1]; exact List.mem_append_left _ hr

theorem NewStk.held (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : InRanges a k L ∨ Outside a k R.rt) :
    InRanges a k L1 ∨ Outside a k R.rt :=
  h.imp (fun h => h.of_subset fun _ hr => hN.mem hr) id

/-- a held range is apart from the new stack's header and array -/
theorem NewStk.apart (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : InRanges a k L ∨ Outside a k R.rt) :
    Apart a k st 24 ∧ Apart a k (freeR M1 st).1 (freeR M1 st).2 := by
  obtain ⟨hin, hap⟩ := hN.hdr
  refine ⟨apart_fresh h hap hin, ?_⟩
  have hl := hN.2.2.2.2.2.2.1
  simp only [freeR, hl, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
  rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
  · have := hN.2.2.2.2.2.2.2.2.1 hc; rw [this, hc]; unfold Apart; omega
  · obtain ⟨hin', hap'⟩ := hN.arr hc
    exact apart_fresh h hap' hin'

/-- the new stack's ranges are apart from anything outside `R.rt` -/
theorem NewStk.out (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : Outside a k R.rt) :
    Outside a k [(st, st + 24)] ∧ (0 < stCap M1 st → Outside a k [(stW M1 st, stW M1 st + 8 * stCap M1 st)]) := by
  refine ⟨?_, fun hc => ?_⟩
  · have := out_inR2 h hN.hdr.1; simp only [outside_cons, outside_nil, and_true]; omega
  · have := out_inR2 h (hN.arr hc).1; simp only [outside_cons, outside_nil, and_true]; omega

theorem NewStk.liveSep (hN : NewStk R L L1 b b1 g M1 st) {w : List (Nat × Nat)} (hL : LiveSep L w)
    (hw : ∀ r ∈ w, Outside r.1 (r.2 - r.1) R.rt) : LiveSep L1 w := by
  intro r hr
  rw [hN.1] at hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hL r hr
  · have hin := (hN.2.1 r hr).1
    refine outside_of_forall fun q hq => ?_
    have := out_inR2 (hw q hq) hin
    omega
end


section
variable {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {M1 : Memory} {st : Nat}

theorem NewStk.outWs (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : Outside a k R.rt) :
    Outside a k (stkWs M1 st) := by
  have hl : stLen M1 st = 0 := hN.2.2.2.2.2.2.1
  have hc0 : stCap M1 st = 0 → stW M1 st = 0 := hN.2.2.2.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := hN.out h
  simp only [stkWs, hl, Nat.mul_zero, Nat.add_zero]
  simp only [outside_cons, outside_nil, and_true] at h1 ⊢
  refine ⟨h1, ?_⟩
  rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
  · have := hc0 hc; simp only [stW, stCap] at this hc ⊢; rw [this, hc]; omega
  · have := h2 hc; simp only [outside_cons, outside_nil, and_true] at this; exact this

theorem NewStk.outL (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : InRanges a k L) :
    Outside a k (stkWs M1 st) ∧ Outside a k [(st + 8, st + 16)] := by
  have hl : stLen M1 st = 0 := hN.2.2.2.2.2.2.1
  have hc0 : stCap M1 st = 0 → stW M1 st = 0 := hN.2.2.2.2.2.2.2.2.1
  have hh := apart_fresh (Or.inl h) hN.hdr.2 hN.hdr.1
  simp only [stkWs, hl, Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
  refine ⟨⟨hh, ?_⟩, by omega⟩
  rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
  · have := hc0 hc; simp only [stW, stCap] at this hc ⊢; rw [this, hc]; omega
  · exact apart_fresh (Or.inl h) (hN.arr hc).2 (hN.arr hc).1
end

theorem stkOK_frame {R : RtInv} {L : List (Nat × Nat)} {st : Nat} {m m' : Memory} {ws : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' ws) (ho : Outside st 24 ws) :
    StkOK m' R L st ∧ stW m' st = stW m st ∧ stLen m' st = stLen m st ∧ stCap m' st = stCap m st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have ew : stW m' st = stW m st := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have el : stLen m' st = stLen m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have ec : stCap m' st = stCap m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  refine ⟨⟨h1, h2, by rw [hF.accessible]; exact h3, h4, ?_, by rw [el, ec]; exact h6, by rw [ec]; exact h7⟩,
    ew, el, ec⟩
  rw [ew, ec]; intro hc
  obtain ⟨a1, a2, a3, a4⟩ := h5 hc
  exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩

theorem stkRs_congr {m m' : Memory} {st : Nat} (hw : stW m' st = stW m st) (hc : stCap m' st = stCap m st) :
    stkRs m' st = stkRs m st := by
  simp only [stkRs]; rw [hw, hc]

theorem liveSep_ext {R : RtInv} {L1 L2 w : List (Nat × Nat)} (hx : LiveExt R L1 L2) (hL : LiveSep L1 w)
    (hw : ∀ r ∈ w, Outside r.1 (r.2 - r.1) R.rt) : LiveSep L2 w := by
  obtain ⟨ns, rfl, hn, -⟩ := hx
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hL r hr
  · refine outside_of_forall fun q hq => ?_
    have := out_inR2 (hw q hq) (hn r hr).1
    omega


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


/-- a range in `R.rt` is outside frames apart from `R.rt` -/
theorem outside_of_rt {R : RtInv} {ws : List (Nat × Nat)} {a k : Nat} (hin : InRanges a k R.rt)
    (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) : Outside a k ws :=
  outside_of_forall fun r hr => by have := out_inR2 (hws r hr) hin; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem newStk_T {R : RtInv} {L : List (Nat × Nat)} {b g : Nat} {m M' : Memory} {d : Nat}
    {rs ws : List (Nat × Nat)}
    (hSh : StkSh m d rs) (hfr : FreshFrom rs L) (hin : ∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt)
    (hinv : R.inv b (L ++ rs) g (view R.rt (L ++ rs) m))
    (hF : MemFrame m M' ws) (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) :
    NewStk R L (L ++ rs) b b g M' d := by
  obtain ⟨h0, h8, h48, hacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hrs⟩ := hSh.ok
  have hhd : InRanges d 24 R.rt := by
    have := hin (d, d + 24) (by rw [hrs]; exact List.mem_cons_self ..)
    simpa only [Nat.add_sub_cancel_left] using this
  have ho := outside_of_rt hhd hws
  have ew : stW M' d = stW m d := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have el : stLen M' d = stLen m d := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have ec : stCap M' d = stCap m d := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have hrE : stkRs M' d = stkRs m d := stkRs_congr ew ec
  unfold NewStk
  rw [hrE, ← hrs, ew, el, ec]
  refine ⟨rfl, fun x hx => ⟨hin x hx, hfr x hx⟩, h0, h8, h48, by rw [hF.accessible]; exact hacc, hlen, hcap, hc0, hw8, hw48,
    fun hc => by rw [hF.accessible]; exact hwacc hc, hdis, by omega, Nat.le_refl _, ?_⟩
  exact RtInv.inv_frame' hF (fun r hr => Or.inl (hws r hr)) hinv


end FvModexp.Amd64.DivNil
