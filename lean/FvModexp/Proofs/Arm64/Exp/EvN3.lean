import FvModexp.Proofs.Arm64.Exp.EvJ
import FvModexp.Proofs.Arm64.Exp.EvCalls

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `rshR` → `z1 = stk.nat(2·max(len m1, len m2))` → `nat3R` (agent infra)

`runN3`: spill `m2` to `280/192/200`, `R2 = len m1` (slot 208), `CMP; CSEL GT` = `max`, `R1 = 2·max` (also to slot
224), `R0 = stk`, `CALL (*stack).nat`. `segN3` (`J4 → J5`): divmc's `StackNat.HypL`; `m1`, `m2` survive
(`LN.stkN`), the scratch `z1` is apart from both (`Scr.apartLN`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem csel_max {l1 l2 : Nat} (h1 : l1 < 2 ^ 40) (h2 : l2 < 2 ^ 40) :
    (if (l1 : Int) < (l2 : Int) then BitVec.ofNat 64 l2 else BitVec.ofNat 64 l1) = BitVec.ofNat 64 (max l1 l2) := by
  by_cases h : l1 < l2
  · rw [if_pos (by omega), Nat.max_eq_right (by omega)]
  · rw [if_neg (by omega), Nat.max_eq_left (by omega)]

theorem two_max {l1 l2 : Nat} (h1 : l1 < 2 ^ 40) (h2 : l2 < 2 ^ 40) :
    BitVec.ofNat 64 (max l1 l2) + BitVec.ofNat 64 (max l1 l2) = BitVec.ofNat 64 (2 * max l1 l2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : max l1 l2 < 2 ^ 40 := by omega
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `rshR` → `(*stack).nat`'s entry -/
theorem runN3 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st q l2 c2 l1 : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 184) 264 true = true)
    (h368 : M.readLE (sp + 368) 8 = st) (h208 : M.readLE (sp + 208) 8 = l1)
    (hq : q < 2 ^ 64) (hl2 : l2 < 2 ^ 40) (hc2 : c2 < 2 ^ 64) (hl1 : l1 < 2 ^ 40)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 rshR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h1 : S.regs 1 = BitVec.ofNat 64 l2) (h2 : S.regs 2 = BitVec.ofNat 64 c2)
    (KN : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 1784176 → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 (2 * max l1 l2) →
      S'.regs 30 = BitVec.ofNat 64 nat3R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 192, sp + 208), (sp + 224, sp + 232), (sp + 280, sp + 288)] → M'.regions = M.regions →
      M'.readLE (sp + 280) 8 = q → M'.readLE (sp + 192) 8 = l2 → M'.readLE (sp + 200) 8 = c2 →
      M'.readLE (sp + 224) 8 = 2 * max l1 l2 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  janus_run [hal, hacc, h368, h208] until [1784176]
  refine KN _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 192, sp + 208)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 224, sp + 232)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 280, sp + 288)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip
  all_goals first | (rw [← eS, hsp]; done) | skip
  all_goals (by_cases hc : l1 < l2 <;>
    simp only [Int.ofNat_lt, hc, ↓reduceIte, setReg_apply, Nat.reduceEqDiff, BitVec.toNat_ofNat])
  all_goals first | omega | skip
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J4` → `J5`** (see the module doc) -/
theorem segN3 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hl16 : ℓ2 s st mp ml + 2 * ml + 3 ≤ 2 ^ 16)
    {rk rk' : Nat} (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → stackNatCost (ℓ2 s st mp ml) (2 * max l1 l2) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K5 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 r : Nat),
      J5 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 r →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 : Nat}
    (h : J4 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hm1 := h.m1
  have hm2 := h.m2
  have hb1 := h.jx.bud
  have hl1 : l1 ≤ ml := nlen_bd' hm1.2.2.2 (by rw [hm1.2.2.1]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hl2 : l2 ≤ ml := by have := hm2.2.1; simp only [a2] at this; omega
  have hq48 : q + 8 * a2 ml (nE s mp ml) ≤ 2 ^ 48 := (hm2.1.2.1 (by simp only [a2]; omega)).2.2.2
  have hacc : S.mem.accessible (sp + 184) 264 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
  refine runN3 ret0 Q sp st q l2 (a2 ml (nE s mp ml)) l1 S.mem hal hsp2 hacc h.jx.esl.2.2.2.2.2.2.2.2.1 h.s208
    (by omega) (by omega) (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r1 h.r2 ?_
  intro S2 M2 f0 fsp f1 f2 f30 f18 f28 f29 fm hF hrg r280 r192 r200 r224
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have hm1' := hown _ _ _ _ hm1
  have hm2' := hown _ _ _ _ hm2
  have hesl := h.jx.esl.keep (fun a k ha => hF.readLE a k (by
    simp only [SlotR] at ha; simp only [outside_cons, outside_nil, and_true]; omega)) (by omega)
  have hS2 : S2.sp = BitVec.ofNat 64 sp := fsp.trans h.jx.esp
  have h28 : S2.regs 28 = BitVec.ofNat 64 g := f28.trans h.jx.e28
  have hsN : S2.sp.toNat = sp := by rw [hS2, BitVec.toNat_ofNat]; omega
  have hgN : (S2.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hmx : 2 * max l1 l2 ≤ 2 * ml := by omega
  have hpre := snPre hP hw2 hkN haN hS2 h28 fm (by omega) (by omega) (bud_pre hb1 (hrk l1 l2 hl1 hl2))
  refine CallNE.stkNatCallL hap hns hsn (ra_ev hap hnf 75 (by decide)) (by rw [f0, stkNat_a]) f30 f1 f2
    (by have := hP.stk0.2.2.2.1; omega) (by omega) (by decide) hpre ?_
  intro s' g1 g2 g3 g4 g5 g6 hpost
  have hmx0 : 0 < 2 * max l1 l2 := by
    have := hm1.2.1; have := h.c1p
    rcases Nat.eq_zero_or_pos l1 with e | e
    · subst e
      have e0 : (0 : Nat) = 2 ^ nE s mp ml := by rw [← hm1.2.2.1]; rfl
      have := Nat.two_pow_pos (nE s mp ml); omega
    · omega
  obtain ⟨L2, b2, hb2, hw3, hscE, hz0, hz1, hz2, hFn, hscC, hLFn, hx, harr⟩ :=
    WC.stkNat hP hw2 hkN haN hsN hgN fm (g6.trans (by rw [fm])) hmx0 hpost
  have hlc := hw2.sok.2.2.2.2.2.1
  have hl := (by rw [hw2.len, hw3.len]; omega : stLen M2 st ≤ stLen s'.mem st)
  have hm1'' := LN.stkN hP hkN haN hFn hLFn hx hlc hl harr hm1'
  have hm2'' := LN.stkN hP hkN haN hFn hLFn hx hlc hl harr hm2'
  have hk := keepC hP hw2 (zs := []) (by simpa only [List.append_nil] using hFn) hkN haN
    (fun _ _ _ _ => by simp only [outside_nil])
  refine K5 s' L2 b2 p1 l1 c1 q l2 _ ⟨⟨g2.trans hS2, g3.trans h28, g4.trans (f29.trans h.jx.e29),
      g5.trans (f18.trans h.jx.e18), hw3, hesl.keep (fun a k ha => hk a k (by simp only [SlotR] at ha; omega))
        (by omega), bud_step hb1 (hrk l1 l2 hl1 hl2) hb2⟩, g1, hz0, hz1, hz2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hm1'', h.c1p, hm2'', h.ap,
    DL.of_scr hw3 hscE rfl (by have := rnd_ge (2 * max l1 l2); omega) (by omega),
    Scr.apartLN hscC hlc hm1' h.c1p, Scr.apartLN hscC hlc hm2' (by simp only [a2]; omega)⟩
  all_goals rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s288
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s208
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s216
  · exact r280
  · exact r192
  · exact r200
  · exact r224

end

end FvModexp.Arm64.ExpEven
