import FvModexp.Proofs.Arm64.Exp.EvJ
import FvModexp.Proofs.Arm64.Exp.EvCalls

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `lshR` → `m2 = stk.nat(ml - n/64)` → `nat2R` (agent infra)

`runN2`: spill `m1` to `288/208/216`, `R0 = stk` (slot 368), `R1 = ml - n/64` (slot 224), `CALL (*stack).nat`.
`segN2` (`J2 → J3`): divmc's `StackNat.HypL`; `m1` survives (`LN.stkN`), the scratch `m2` is a destination apart
from `m1` (`Scr.apartLN`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `lshR` → `(*stack).nat`'s entry -/
theorem runN2 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st v p1 l1 c1 : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 184) 256 true = true)
    (h368 : M.readLE (sp + 368) 8 = st) (h224 : M.readLE (sp + 224) 8 = v)
    (hp1 : p1 < 2 ^ 64) (hl1 : l1 < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 lshR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 p1) (h1 : S.regs 1 = BitVec.ofNat 64 l1) (h2 : S.regs 2 = BitVec.ofNat 64 c1)
    (KN : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 1784176 → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 v → S'.regs 30 = BitVec.ofNat 64 nat2R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 208, sp + 224), (sp + 288, sp + 296)] → M'.regions = M.regions →
      M'.readLE (sp + 288) 8 = p1 → M'.readLE (sp + 208) 8 = l1 → M'.readLE (sp + 216) 8 = c1 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  have hv : S.mem.readLE (sp + 224) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have hs : S.mem.readLE (sp + 368) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  janus_run [hal, hacc, h368, h224] until [1784176]
  refine KN _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 208, sp + 224)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 288, sp + 296)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip
  rw [← eS, hsp]

theorem stkNat_a : segAddr Extracted.program StackNat.fn = 1784176 := by decide

theorem rnd_ge (n : Nat) : n ≤ StackNat.rnd n := by unfold StackNat.rnd; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J2` → `J3`** (see the module doc) -/
theorem segN2 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hl16 : stLen s.mem st + StackNat.rnd (a1 (nE s mp ml)) + a2 ml (nE s mp ml) + 3 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : stackNatCost (stLen s.mem st + StackNat.rnd (a1 (nE s mp ml))) (a2 ml (nE s mp ml)) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K3 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q : Nat),
      J3 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 : Nat}
    (h : J2 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have ha2 : 0 < a2 ml (nE s mp ml) ∧ a2 ml (nE s mp ml) ≤ 128 := by simp only [a2]; omega
  have hw := h.jx.wc
  have hm1 := h.m1
  have hc1 := h.c1p
  have hb1 := h.jx.bud
  have hp1 : p1 + 8 * c1 ≤ 2 ^ 48 := (hm1.1.2.1 hc1).2.2.2
  have hc40 : c1 < 2 ^ 40 := hm1.1.1
  have hl1 : l1 ≤ c1 := hm1.2.1
  have hacc : S.mem.accessible (sp + 184) 256 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
  refine runN2 ret0 Q sp st (a2 ml (nE s mp ml)) p1 l1 c1 S.mem hal hsp2 hacc h.jx.esl.2.2.2.2.2.2.2.2.1 h.s224
    (by omega) (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r1 h.r2 ?_
  intro S2 M2 f0 fsp f1 f2 f30 f18 f28 f29 fm hF hrg r288 r208 r216
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [OwnR] <;> omega)
  have hm1' := hown _ _ _ _ hm1
  have hesl := h.jx.esl.keep (fun a k ha => hF.readLE a k (by
    simp only [SlotR] at ha; simp only [outside_cons, outside_nil, and_true]; omega)) (by omega)
  have hS2 : S2.sp = BitVec.ofNat 64 sp := fsp.trans h.jx.esp
  have h28 : S2.regs 28 = BitVec.ofNat 64 g := f28.trans h.jx.e28
  have hsN : S2.sp.toNat = sp := by rw [hS2, BitVec.toNat_ofNat]; omega
  have hgN : (S2.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hpre := snPre hP hw2 hkN haN hS2 h28 fm (by omega) hl16 (by omega)
  refine CallNE.stkNatCallL hap hns hsn (ra_ev hap hnf 60 (by decide)) (by rw [f0, stkNat_a]) f30 f1 f2
    (by have := hP.stk0.2.2.2.1; omega) (by omega) (by decide) hpre ?_
  intro s' g1 g2 g3 g4 g5 g6 hpost
  obtain ⟨L2, b2, hb2, hw3, hscE, hz0, hz1, hz2, hFn, hscC, hLFn, hx, harr⟩ :=
    WC.stkNat hP hw2 hkN haN hsN hgN fm (g6.trans (by rw [fm])) ha2.1 hpost
  have hlc := hw2.sok.2.2.2.2.2.1
  have hm1'' := LN.stkN hP hkN haN hFn hLFn hx hlc (by rw [hw2.len, hw3.len]; omega) harr hm1'
  have hk := keepC hP hw2 (zs := []) (by simpa only [List.append_nil] using hFn) hkN haN
    (fun _ _ _ _ => by simp only [outside_nil])
  refine K3 s' L2 b2 p1 l1 c1 _ ⟨⟨g2.trans hS2, g3.trans h28, g4.trans (f29.trans h.jx.e29),
      g5.trans (f18.trans h.jx.e18), hw3, hesl.keep (fun a k ha => hk a k (by simp only [SlotR] at ha; omega))
        (by omega), by omega⟩, g1, hz0, hz1, hz2, ?_, ?_, ?_, hm1'', hc1,
    DL.of_scr hw3 hscE rfl (by have := rnd_ge (a2 ml (nE s mp ml)); omega) (by omega),
    Scr.apartLN hscC hlc hm1' hc1⟩
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact r288
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact r208
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact r216

end

end FvModexp.Arm64.ExpEven
