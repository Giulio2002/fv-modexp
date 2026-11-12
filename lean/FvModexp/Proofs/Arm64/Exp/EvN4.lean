import FvModexp.Proofs.Arm64.Exp.EvJ2
import FvModexp.Proofs.Arm64.Exp.EvCalls

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `exp1R` → `z2 = stk.nat(2·max(len m1, len m2))` → `nat4R` (agent infra)

`runN4`: spill `z1` to `264/152/160`, `R0 = stk`, `R1 = 2·max` (slot 224), `CALL (*stack).nat`. `segN4` (`J6 → J7`):
divmc's `StackNat.HypL`; `m1`, `m2`, `z1` survive (`LN.stkN`), the scratch `z2` is apart
from all of them (`Scr.apartLN`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `exp1R` → `(*stack).nat`'s entry -/
theorem runN4 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st pz lz cz k : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 136) 312 true = true)
    (h368 : M.readLE (sp + 368) 8 = st) (h224 : M.readLE (sp + 224) 8 = k)
    (hp : pz < 2 ^ 64) (hl : lz < 2 ^ 64) (hc : cz < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 exp1R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pz) (h1 : S.regs 1 = BitVec.ofNat 64 lz) (h2 : S.regs 2 = BitVec.ofNat 64 cz)
    (KN : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 1784176 → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 k →
      S'.regs 30 = BitVec.ofNat 64 nat4R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 152, sp + 168), (sp + 264, sp + 272)] → M'.regions = M.regions →
      M'.readLE (sp + 264) 8 = pz → M'.readLE (sp + 152) 8 = lz → M'.readLE (sp + 160) 8 = cz →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  janus_run [hal, hacc, h368, h224] until [1784176]
  refine KN _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 152, sp + 168)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 264, sp + 272)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J6` → `J7`** (see the module doc) -/
theorem segN4 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hl16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → ℓ3 s st mp ml l1 l2 + 2 * ml + 3 ≤ 2 ^ 16)
    {rk rk' : Nat} (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → stackNatCost (ℓ3 s st mp ml l1 l2) (2 * max l1 l2) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K7 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz t : Nat),
      J7 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz t →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz : Nat}
    (h : J6 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hl1 : l1 ≤ ml := nlen_bd' h.m1.2.2.2 (by rw [h.m1.2.2.1]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hl2 : l2 ≤ ml := by have := h.m2.2.1; simp only [a2] at this; omega
  have hl10 : 0 < l1 := by
    rcases Nat.eq_zero_or_pos l1 with e | e
    · have e0 : (0 : Nat) = 2 ^ nE s mp ml := by rw [← h.m1.2.2.1, e]; rfl
      have := Nat.two_pow_pos (nE s mp ml); omega
    · exact e
  have hml := hP.2.2.2.2.2.2.1
  have hcz := h.z1.1.1
  have hlz := h.z1.2.1
  have hacc : S.mem.accessible (sp + 136) 312 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
  have hpz : pz < 2 ^ 64 := h.pz64
  refine runN4 ret0 Q sp st pz lz cz (2 * max l1 l2) S.mem hal hsp2 hacc h.jx.esl.2.2.2.2.2.2.2.2.1 h.s224
    hpz (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r1 h.r2 ?_
  intro S2 M2 f0 fsp f1 f2 f30 f18 f28 f29 fm hF hrg r264 r152 r160
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [OwnR] <;> omega)
  have hesl := h.jx.esl.keep (fun a k ha => hF.readLE a k (by
    simp only [SlotR] at ha; simp only [outside_cons, outside_nil, and_true]; omega)) (by omega)
  have hS2 : S2.sp = BitVec.ofNat 64 sp := fsp.trans h.jx.esp
  have h28 : S2.regs 28 = BitVec.ofNat 64 g := f28.trans h.jx.e28
  have hsN : S2.sp.toNat = sp := by rw [hS2, BitVec.toNat_ofNat]; omega
  have hgN : (S2.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hpre := snPre hP hw2 hkN haN hS2 h28 fm (by omega) (by have := hl16 l1 l2 hl1 hl2; omega)
    (bud_pre hb1 (hrk l1 l2 hl1 hl2))
  refine CallNE.stkNatCallL hap hns hsn (ra_ev hap hnf 93 (by decide)) (by rw [f0, stkNat_a]) f30 f1 f2
    (by have := hP.stk0.2.2.2.1; omega) (by omega) (by decide) hpre ?_
  intro s' g1 g2 g3 g4 g5 g6 hpost
  have hmx0 : 0 < 2 * max l1 l2 := by omega
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  obtain ⟨L2, b2, hb2, hw3, hscE, hz0, hz1, hz2, hFn, hscC, hLFn, hx, harr⟩ :=
    WC.stkNat hP hw2 hkN haN hsN hgN fm (g6.trans (by rw [fm])) hmx0 hpost
  have hlc := hw2.sok.2.2.2.2.2.1
  have hl := (by rw [hw2.len, hw3.len]; omega : stLen M2 st ≤ stLen s'.mem st)
  have kN : ∀ {q l c v : Nat}, LN R L s.mem st M2 L1 q l c v → LN R L s.mem st s'.mem L2 q l c v :=
    fun hq => LN.stkN hP hkN (by omega) hFn hLFn hx hlc hl harr hq
  have hk := keepC hP hw2 (zs := []) (by simpa only [List.append_nil] using hFn) hkN (by omega)
    (fun _ _ _ _ => by simp only [outside_nil])
  have hm1 := hown _ _ _ _ h.m1
  have hm2 := hown _ _ _ _ h.m2
  have hz := hown _ _ _ _ h.z1
  refine K7 s' L2 b2 p1 l1 c1 q l2 pz lz cz _ ⟨⟨g2.trans hS2, g3.trans h28, g4.trans (f29.trans h.jx.e29),
      g5.trans (f18.trans h.jx.e18), hw3, hesl.keep (fun a k ha => hk a k (by simp only [SlotR] at ha; omega))
        (by omega), bud_step hb1 (hrk l1 l2 hl1 hl2) hb2⟩, g1, hz0, hz1, hz2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    kN hm1, h.c1p, kN hm2, h.ap, kN hz, h.pz64, h.za1, h.za2,
    DL.of_scr hw3 hscE rfl (by have := rnd_ge (2 * max l1 l2); omega) (by omega),
    Scr.apartLN hscC hlc hm1 h.c1p, Scr.apartLN hscC hlc hm2 ha2, fun c0 => Scr.apartLN hscC hlc hz c0⟩
  all_goals rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s288
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s208
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s216
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s280
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s192
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s200
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.s224
  · exact r264
  · exact r152
  · exact r160

end

end FvModexp.Arm64.ExpEven
