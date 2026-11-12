import FvModexp.Proofs.Arm64.Exp.NNilD
import FvModexp.Proofs.Arm64.Exp.NCPre

/-!
# `nat.expNN` (arm64), `stk == nil`: the stack-given precondition at the virtual entry (`npreV`)

After `Get`/`newobject` the downstream code (from the `rem` entry / `J5`) is that of the stack-given path, with the new
stack `st` and the live set `L1 = L ++ stkRs M1 st`. `npreV`: `PreNil` at the entry state `s` and `NewStk` at the
memory `M1` of that point (`s.mem → M1` writes only `R.rt` and the window) give `NPre … st … {s with mem := M1}` (the
"virtual entry"), so `remPath`/`fromJ5` apply unchanged. `zokV`: the same for the alias facts of `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

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
    Apart a k st 24 ∧ Apart a k (W4En.free M1 st).1 (W4En.free M1 st).2 := by
  obtain ⟨hin, hap⟩ := hN.hdr
  refine ⟨apart_fresh h hap hin, ?_⟩
  have hl := hN.2.2.2.2.2.2.1
  simp only [W4En.free, hl, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
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

set_option maxRecDepth 20000 in
/-- an operand `NE0` at the entry ⇒ `NE` at the virtual entry -/
theorem ne_v {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g sp K st : Nat} {M1 : Memory} {a k : Nat}
    (h : NE0 R L sp K a k) (hN : NewStk R L L1 b b1 g M1 st) : NE R L1 sp K st M1 a k :=
  ⟨hN.held h.1, h.2, (hN.apart h.1).1, (hN.apart h.1).2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z`'s alias facts at the virtual entry -/
theorem zokV {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g sp K st zp zc xp xl yp yl mp n : Nat} {M M1 : Memory}
    (h : ZOK0 R L g sp K zp zc xp xl yp yl mp n M) (hN : NewStk R L L1 b b1 g M1 st)
    (hacc : ∀ a k w, M1.accessible a k w = M.accessible a k w) :
    ZOK R L1 g sp K st zp zc xp xl yp yl mp n M1 := by
  obtain ⟨hE, ha, h48, h8, hL, hg, hm, hy, hx, hgA⟩ := h
  refine ⟨ne_v hE hN, by rw [hacc]; exact ha, h48, h8, fun hc => ?_, hg, hm, hy, hx, hgA⟩
  obtain ⟨a1, a2, a3, a4⟩ := hL hc
  exact ⟨a1, hN.held a2, by rw [hacc]; exact a3, a4⟩

/-- the data words read by `Globals` survive a frame of `R.rt` and the window -/
theorem globals_v {R : RtInv} {m m' : Memory} {w : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' (R.rt ++ w)) : RunIface.Globals R m' w := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt.of_sub (by omega) (by omega), hgw.of_sub (by omega) (by omega)⟩)
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

/-- an operand's array (held, apart from the window) keeps its value and normal form -/
theorem opnd_v {R : RtInv} {L : List (Nat × Nat)} {sp K p k : Nat} {M M1 : Memory}
    (h : NE0 R L sp K p (8 * k)) (hLF : LiveFrame M M1 L []) (hF : MemFrame M M1 (R.rt ++ wN sp K))
    (hN : NatNorm M p k) : natVal M1 p k = natVal M p k ∧ NatNorm M1 p k := by
  have e : M1.readLE p (8 * k) = M.readLE p (8 * k) := rd_held h.1 hLF hF h.2
  refine ⟨e, ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact Or.inl hk0
  rcases hN with h0 | h1
  · exact Or.inl h0
  · right
    rw [rd_held (held_sub h.1 (by omega) (by omega)) hLF hF (by have := h.2; unfold Apart at this ⊢; omega)]
    exact h1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the virtual entry**: `PreNil` at `s` and the new stack at `M1` ⇒ `NPre` at `{s with mem := M1}` -/
theorem npreV {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L []) (hrg : M1.regions = s.mem.regions) :
    NPre R b1 L1 K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow
      { s with mem := M1 } := by
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, hd, hsv⟩, hK20, hG, ⟨hro, -⟩, hwT, hslow,
    hn, hn128, hnmc, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyc, hxO, hxa, hx48, hxN, hxl, hxp, hxc,
    hzp, hzlc, hzc, -, hali, hgAO, ⟨op, hone⟩, -, hwb, hb1, hb2, hb3, hb4, hbud, -, -, -⟩ := hP
  have hN' := hN
  obtain ⟨-, -, hst0, hst8, hst48, hstacc, hlen, hcap40, hc0, hw8, hw48, hwacc, hdis, hbb, -, hinv⟩ := hN'
  have hacM : ∀ a k w, M1.accessible a k w = s.mem.accessible a k w := fun a k w => hF.accessible a k w
  have hout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  simp only [outside_cons] at hgo
  have hwrt' : ∀ r ∈ [(sp - K, sp + 1432)], Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only; rw [show sp + 1432 - (sp - K) = K + 1432 by omega]
    exact hout
  have hmv := opnd_v hmO hLF hF hmN
  have hyv := opnd_v hyO hLF hF hyN
  have hxv := opnd_v hxO hLF hF hxN
  -- the new stack's header/array vs the window, the guard word, `wbA`, `gA`
  have hstw : Apart st 24 (sp - K) (K + 1432) := ((hN.apart (Or.inr hout)).1).symm
  have hstg : Apart st 24 (g + 16) 8 := ((hN.apart (Or.inr hgo.2)).1).symm
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, -, hgrt, -, -, hwbrt, -⟩ := hG'
  have hwbA : Apart st 24 StackNat.wbA 4 := ((hN.apart (Or.inr hwbrt)).1).symm
  have hfr0 : W4En.free M1 st = (stW M1 st, 8 * stCap M1 st) := by
    simp only [W4En.free, hlen, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
  have hfgA : Apart (W4En.free M1 st).1 (W4En.free M1 st).2 RunIface.gA 32 := ((hN.apart (Or.inr hgrt)).2).symm
  have hstfr : Apart st 24 (W4En.free M1 st).1 (W4En.free M1 st).2 := by rw [hfr0]; exact hdis
  have harr : 0 < stCap M1 st → Apart (stW M1 st) (8 * stCap M1 st) (sp - K) (K + 1432) ∧
      Apart (stW M1 st) (8 * stCap M1 st) (g + 16) 8 := fun hc => by
    have h1 := (hN.apart (Or.inr hout)).2; have h2 := (hN.apart (Or.inr hgo.2)).2
    rw [hfr0] at h1 h2; exact ⟨h1.symm, h2.symm⟩
  -- the stack's `StkOK`
  have hhdr : (st, st + 24) ∈ L1 := by rw [hN.1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hsok : StkOK M1 R L1 st := by
    refine ⟨hst8, Or.inl ⟨_, hhdr, Nat.le_refl _, Nat.le_refl _⟩, hstacc, hst48, fun hc => ?_, by omega, hcap40⟩
    have hm : (stW M1 st, stW M1 st + 8 * stCap M1 st) ∈ L1 := by
      rw [hN.1]; refine List.mem_append_right _ ?_
      simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, List.mem_singleton, true_or, or_true]
    exact ⟨hw8, Or.inl ⟨_, hm, Nat.le_refl _, Nat.le_refl _⟩, hwacc hc, hw48⟩
  -- `natOne`
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11⟩ := hone
  have o7w : Outside EvenHyp.natOneA 24 [(sp - K, sp + 1432)] := by
    simp only [outside_cons, outside_nil, and_true] at o7 ⊢; exact o7.1
  have hrdO : ∀ {a k : Nat}, Outside a k R.rt → Outside a k [(sp - K, sp + 1432)] → M1.readLE a k = s.mem.readLE a k :=
    fun h1 h2 => hF.readLE _ _ (by
      rw [outside_append]; refine ⟨h1, ?_⟩
      simp only [wN, outside_cons, outside_nil, and_true] at h2 ⊢; omega)
  have hopw : Outside op 8 [(sp - K, sp + 1432)] := by
    simp only [outside_cons, outside_nil, and_true] at o11 ⊢; exact o11.1
  have hone' : EvenHyp.NatOne R L1 M1 op ([(sp - K, sp + 1432), (zp, zp + 8 * zc)] ++ stkWs M1 st) ∧
      EvenHyp.StkApart M1 st op 8 := by
    have hoA := hN.apart o10
    have hnO := hN.out o6
    have hoO := hN.apart o10
    refine ⟨⟨?_, ?_, ?_, ?_, by rw [hacM]; exact o5, o6, ?_, by rw [hacM]; exact o8, o9, hN.held o10, ?_⟩, fun _ => ?_⟩
    · rw [hrdO (o6.of_sub (by omega) (by omega)) (o7w.of_sub (by omega) (by omega))]; exact o1
    · rw [hrdO (o6.of_sub (by omega) (by omega)) (o7w.of_sub (by omega) (by omega))]; exact o2
    · rw [hrdO (o6.of_sub (by omega) (by omega)) (o7w.of_sub (by omega) (by omega))]; exact o3
    · rw [rd_held o10 hLF hF (by simp only [outside_cons, outside_nil, and_true] at hopw; unfold Apart; omega)]
      exact o4
    · rw [outside_append]; refine ⟨o7, ?_⟩
      simp only [stkWs, hlen, Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
      refine ⟨by have := hnO.1; simpa only [outside_cons, outside_nil, and_true] using this, ?_⟩
      rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
      · rw [hc0 hc, hc]; omega
      · have := hnO.2 hc; simpa only [outside_cons, outside_nil, and_true] using this
    · rw [outside_append]; refine ⟨o11, ?_⟩
      simp only [stkWs, hlen, Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
      have h1 := hoA.1; have h2 := hoA.2; rw [hfr0] at h2; unfold Apart at h1 h2; omega
    · refine ⟨hoA.1, fun _ => ?_⟩
      have h2 := hoA.2; simp only [W4En.free] at h2; rw [hlen] at h2 ⊢; exact h2
  refine ⟨⟨hs1, hs28, hg1, by rw [hacM]; exact hg2, ?_, ?_, hal, hK4, hKs, hsp2, by rw [hacM]; exact hacc,
    hwrt, hN.liveSep hLs hwrt', ?_, hsv⟩, hK20, globals_v hG (hF.mono fun a k ho => by
      rw [outside_append] at ho ⊢; refine ⟨ho.1, ?_⟩; have := ho.2
      simp only [wN, outside_cons, outside_nil, and_true] at this ⊢; omega), hro, hwT, hslow, hn, hn128, hnmc, hmc,
    ne_v hmO hN, by rw [hacM]; exact hma, hm48, hmv.2,
    ne_v hyO hN, by rw [hacM]; exact hya, hy48, hyv.2, hyl, hyc,
    ne_v hxO hN, by rw [hacM]; exact hxa, hx48, hxv.2, hxl, hxp, hxc, hzp, hzlc, hzc, ?_, ne_v hgAO hN,
    ⟨op, hone'⟩, hst0, by omega, hsok, hstw, hstg, harr, hc0, by rw [hacM]; exact hwb, hwbA, hstfr, hfgA, ?_⟩
  · show M1.readLE (g + 16) 8 + K < sp
    rw [hrdO hgo.2 (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hg3
  · simp only [outside_cons]; exact hgo
  · exact dataLoaded_frame hd hrg hro hF (fun r hr _ => by
      simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega))
  · intro hc
    rcases hali hc with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (zokV h hN hacM))
  · simp only [hlen, hmv.1]
    exact ⟨by omega, by omega, by omega, by omega, by omega, hinv⟩

end FvModexp.Arm64.ExpN
