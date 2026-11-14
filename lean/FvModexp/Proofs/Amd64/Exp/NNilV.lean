import FvModexp.Proofs.Amd64.Exp.NNilD
import FvModexp.Proofs.Amd64.Exp.NCPre
import FvModexp.Proofs.Amd64.Exp.NOddP

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the stack-given precondition at the virtual entry (`npreV`) (agent expmc s74;
twin of `Arm64.ExpN.npreV`)

After `Get`/`newobject` the downstream code (from the `rem` entry / `J4`) is that of the stack-given path, with the new
stack `st` and the live set `L1 = L ++ stkRs M1 st` (`DivNil.NewStk`). `npreV`: `PreNil` at the entry state `s`, the
`x` facts and `NewStk` at the memory `M1` of that point (`s.mem → M1` writes only `R.rt` and the window) give
`NPre … st … {s with mem := M1}` (the "virtual entry") and `XFacts` for `L1`, so `remPath`/`fromJ4E` apply
unchanged. `zokV`: the same for the alias facts of `z`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

theorem ne_v {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g sp K st : Nat} {M1 : Janus.Arm64.Memory} {a k : Nat}
    (h : NE0 R L sp K a k) (hN : NewStk R L L1 b b1 g M1 st) : NE R L1 sp K st M1 a k :=
  ⟨hN.held h.1, h.2, (hN.apart h.1).1, (hN.apart h.1).2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z`'s alias facts at the virtual entry -/
theorem zokV {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g fs sp K st zp zc xp xc yp yl mp n : Nat}
    {M M1 : Janus.Arm64.Memory}
    (h : ZOK0 R L g fs sp K zp zc xp xc yp yl mp n M) (hN : NewStk R L L1 b b1 g M1 st)
    (hacc : ∀ a k w, M1.accessible a k w = M.accessible a k w) :
    ZOK R L1 g fs sp K st zp zc xp xc yp yl mp n M1 := by
  obtain ⟨hE, ha, h48, h8, hL, hg, hf, hm, hy, hx, hgA⟩ := h
  refine ⟨ne_v hE hN, by rw [hacc]; exact ha, h48, h8, fun hc => ?_, hg, hf, hm, hy, hx, hgA⟩
  obtain ⟨a1, a2, a3, a4⟩ := hL hc
  exact ⟨a1, hN.held a2, by rw [hacc]; exact a3, a4⟩

/-- the data words read by `Globals` survive a frame of `R.rt` and the window -/
theorem globals_v {R : RtInv} {m m' : Janus.Arm64.Memory} {w : List (Nat × Nat)} (h : RunIface.Globals R m w)
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
    rw [this]; exact h40'

/-- an operand's array (held, apart from the window) keeps its value and normal form -/
theorem opnd_v {R : RtInv} {L : List (Nat × Nat)} {sp K p k : Nat} {M M1 : Janus.Arm64.Memory}
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

/-- an opaque wrapper (keeps a hypothesis away from `omega`) -/
structure BoxV (P : Prop) : Prop where
  un : P

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the virtual entry**: `PreNil` at `s`, the `x` facts and the new stack at `M1` ⇒ `NPre` and `XFacts` at
`{s with mem := M1}` -/
theorem npreV {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hX : NHyp.XFacts R L xp xl xc)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Janus.Arm64.Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L []) (hrg : M1.regions = s.mem.regions)
    (hA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → M1.readLE a k = s.mem.readLE a k)
    (hx0 : xl ≠ 0) (hy0 : yl ≠ 0) :
    NPre R b1 L1 K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow
      { s with mem := M1 } ∧ NHyp.XFacts R L1 xp xl xc := by
  obtain ⟨⟨hs4, hs14, hsfs, hx15, hdf, hK1, hK2, hce, hsv⟩, hG, -, hwT, hwTy, hadx, hslow,
    hry, hryl, hryc, hrm, hrn, hrmc, hn, hn128, hnmc, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyc,
    hxO, hxa, hx48, hxN, hxl, hxlc, hxc, hzp, ⟨hzlc, hxz, hxlz, hxcz⟩, hzc, hali, -, hgAO, hone0, -, hwb,
    hb1, hb2, hb3, hb4, hbud, hob, -, hgn⟩ := hP
  have hbudB : BoxV _ := ⟨hbud⟩
  have hobB : BoxV _ := ⟨hob⟩
  clear hbud hob
  replace hyO := hyO (by omega); replace hya := hya (by omega); replace hy48 := hy48 (by omega)
  replace hxO := hxO (by omega); replace hxa := hxa (by omega); replace hx48 := hx48 (by omega)
  have hzc0 : 0 < zc := by omega
  obtain ⟨op, hone⟩ := hone0 hzc0
  clear hone0
  have hN' := hN
  obtain ⟨-, -, hst0, hst8, hst48, hstacc, hlen, hcap40, hc0, hw8, hw48, hwacc, hdis, hbb, hbb', hinv⟩ := hN'
  have hacM : ∀ a k w, M1.accessible a k w = s.mem.accessible a k w := fun a k w => hF.accessible a k w
  have hce' := hce
  obtain ⟨hal, hKs, hsp2, hacc, hg1, hg2, hg3, hout, hgw, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce'
  have hwrt' : ∀ r ∈ [(sp - K, sp + 0x510)], Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only; rw [show sp + 0x510 - (sp - K) = K + 0x510 by omega]
    exact hout
  have hmv := opnd_v hmO hLF hF hmN
  have hyv := opnd_v hyO hLF hF hyN
  have hxO' : NE0 R L sp K xp (8 * xl) :=
    ⟨held_sub hxO.1 (Nat.le_refl _) (by omega), by have := hxO.2; unfold Apart at this ⊢; omega⟩
  have hxv := opnd_v hxO' hLF hF hxN
  have hstw : Apart st 24 (sp - K) (K + 0x510) := ((hN.apart (Or.inr hout)).1).symm
  have hstg : Apart st 24 (g + 16) 8 := ((hN.apart (Or.inr hgrt)).1).symm
  have hstf : Apart st 24 (fs - 8) 8 := ((hN.apart (Or.inr f5)).1).symm
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, -, -, hwbrt, -⟩ := hG'
  have hwbA : Apart st 24 StackNat.wbA 4 := ((hN.apart (Or.inr hwbrt)).1).symm
  have hfr0 : W4En.free M1 st = (stW M1 st, 8 * stCap M1 st) := by
    simp only [W4En.free, hlen, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
  have hfgA : Apart (W4En.free M1 st).1 (W4En.free M1 st).2 RunIface.gA 32 := ((hN.apart (Or.inr hgArt)).2).symm
  have hffs : Apart (W4En.free M1 st).1 (W4En.free M1 st).2 (fs - 8) 8 := ((hN.apart (Or.inr f5)).2).symm
  have hstfr : Apart st 24 (W4En.free M1 st).1 (W4En.free M1 st).2 := by rw [hfr0]; exact hdis
  have harr : 0 < stCap M1 st → Apart (stW M1 st) (8 * stCap M1 st) (sp - K) (K + 0x510) ∧
      Apart (stW M1 st) (8 * stCap M1 st) (g + 16) 8 ∧ Apart (stW M1 st) (8 * stCap M1 st) (fs - 8) 8 := fun hc => by
    have h1 := (hN.apart (Or.inr hout)).2; have h2 := (hN.apart (Or.inr hgrt)).2; have h3 := (hN.apart (Or.inr f5)).2
    simp only [freeR, hlen, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at h1 h2 h3
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  have hhdr : (st, st + 24) ∈ L1 := by rw [hN.1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hsok : StkOK M1 R L1 st := by
    refine ⟨hst8, Or.inl ⟨_, hhdr, Nat.le_refl _, Nat.le_refl _⟩, hstacc, hst48, fun hc => ?_, by omega, hcap40⟩
    have hm : (stW M1 st, stW M1 st + 8 * stCap M1 st) ∈ L1 := by
      rw [hN.1]; refine List.mem_append_right _ ?_
      simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, List.mem_singleton, true_or, or_true]
    exact ⟨hw8, Or.inl ⟨_, hm, Nat.le_refl _, Nat.le_refl _⟩, hwacc hc, hw48⟩
  -- `natOne`
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11⟩ := hone
  have o7w : Outside EvenHyp.natOneA 24 [(sp - K, sp + 0x510)] := by
    simp only [outside_cons, outside_nil, and_true] at o7 ⊢; exact o7.1
  have hrdO : ∀ {a k : Nat}, Outside a k R.rt → Outside a k [(sp - K, sp + 0x510)] →
      M1.readLE a k = s.mem.readLE a k :=
    fun h1 h2 => hF.readLE _ _ (by
      rw [outside_append]; refine ⟨h1, ?_⟩
      simp only [wN, outside_cons, outside_nil, and_true] at h2 ⊢; omega)
  have hopw : Outside op 8 [(sp - K, sp + 0x510)] := by
    simp only [outside_cons, outside_nil, and_true] at o11 ⊢; exact o11.1
  have hn1 : M1.readLE EvenHyp.natOneA 8 = s.mem.readLE EvenHyp.natOneA 8 :=
    hrdO (o6.of_sub (by omega) (by omega)) (o7w.of_sub (by omega) (by omega))
  have hone' : EvenHyp.NatOne R L1 M1 op ([(sp - K, sp + 0x510), (zp, zp + 8 * zc)] ++ ExpHyp.stWs M1 st) ∧
      NHyp.StkApart M1 st op 8 := by
    have hoA := hN.apart o10
    have hnO := hN.out o6
    refine ⟨⟨?_, ?_, ?_, ?_, by rw [hacM]; exact o5, o6, ?_, by rw [hacM]; exact o8, o9, hN.held o10, ?_⟩, fun _ => ?_⟩
    · rw [hn1]; exact o1
    · rw [hrdO (o6.of_sub (by omega) (by omega)) (o7w.of_sub (by omega) (by omega))]; exact o2
    · rw [hrdO (o6.of_sub (by omega) (by omega)) (o7w.of_sub (by omega) (by omega))]; exact o3
    · rw [rd_held o10 hLF hF (by simp only [outside_cons, outside_nil, and_true] at hopw; unfold Apart; omega)]
      exact o4
    · rw [outside_append]; refine ⟨o7, ?_⟩
      simp only [ExpHyp.stWs, stkWs, hlen, Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
      refine ⟨by have := hnO.1; simpa only [outside_cons, outside_nil, and_true] using this, ?_⟩
      rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
      · rw [hc0 hc, hc]; omega
      · have := hnO.2 hc; simpa only [outside_cons, outside_nil, and_true] using this
    · rw [outside_append]; refine ⟨o11, ?_⟩
      simp only [ExpHyp.stWs, stkWs, hlen, Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
      have h1 := hoA.1; have h2 := hoA.2; simp only [freeR, hlen] at h2; unfold Apart at h1 h2; omega
    · refine ⟨hoA.1, fun _ => ?_⟩
      have h2 := hoA.2; simp only [freeR] at h2; rw [hlen] at h2 ⊢; exact h2
  have hws : ∀ r ∈ wN sp K, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have ce1 := CallW.CEnv.frame hce hF hrg hws
    (by unfold Apart at hgw; simp only [wN, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [wN, outside_cons, outside_nil, and_true]; omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, -, c12, c13, c14, c15, c16, c17, c18, c19⟩ := ce1
  have hxA : Apart xp (8 * xc) st 24 ∧ Apart xp (8 * xc) (freeR M1 st).1 (freeR M1 st).2 := hN.apart hxO.1
  refine ⟨⟨⟨hs4, hs14, hsfs, hx15, hdf, hK1, hK2,
      ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hN.liveSep hLs hwrt', c12, c13, c14, c15, c16, c17, c18, c19⟩, hsv⟩,
    globals_v hG (hF.mono fun a k ho => by
      rw [outside_append] at ho ⊢; refine ⟨ho.1, ?_⟩; have := ho.2
      simp only [wN, outside_cons, outside_nil, and_true] at this ⊢; omega), hwT, hwTy,
    by rw [hacM]; exact hadx, hslow, (hA _ _ (by omega) (by omega)).trans hry, (hA _ _ (by omega) (by omega)).trans hryl,
    (hA _ _ (by omega) (by omega)).trans hryc, (hA _ _ (by omega) (by omega)).trans hrm,
    (hA _ _ (by omega) (by omega)).trans hrn, (hA _ _ (by omega) (by omega)).trans hrmc, hn, hn128, hnmc, hmc,
    ne_v hmO hN, by rw [hacM]; exact hma, hm48, hmv.2,
    ne_v hyO hN, by rw [hacM]; exact hya, hy48, hyv.2, hyl, hyc,
    ne_v hxO hN, by rw [hacM]; exact hxa, hx48, hxv.2, hxl, hxlc, hxc, hzp, hzlc, hzc, ⟨?_, ?_⟩, ne_v hgAO hN,
    ⟨op, hone'⟩, hst0, by omega, hsok, hstw, hstg, hstf, harr, hc0, by rw [hacM]; exact hwb, hwbA, hstfr, hfgA,
    hffs, ?_⟩, ?_⟩
  · intro hc
    rcases hali hc with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (zokV h hN hacM))
  · have := hxO.2; subst hxz; subst hxcz
    simp only [outside_cons, outside_nil, and_true]; unfold Apart at this; omega
  · simp only [hlen, hmv.1]
    have hbud := hbudB.un
    refine ⟨by omega, by omega, by omega, by omega, by omega, oBud_mono hobB.un (by omega), hinv, ?_⟩
    refine ⟨hX.2, by rw [hn1]; exact hgn, by rw [hacM]; exact hadx, by rw [hacM]; exact hxa, hxA.1, hxA.2⟩
  · obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hX
    exact ⟨⟨a1, a2, fun h => ⟨hN.held (a3 h).1, (a3 h).2⟩⟩, a4⟩

end FvModexp.Amd64.ExpN
