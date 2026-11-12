import FvModexp.Proofs.Arm64.Exp.P2W2AT
import FvModexp.Proofs.Arm64.Exp.P2W2Ent
import FvModexp.Proofs.Arm64.Exp.P2W2N
import FvModexp.Proofs.Arm64.Exp.P2W2PC

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): from the entry to the return of the table call (agent infra)

`entP` = `ent` (prologue, `stk.reserve(8w)`) ∘ `segN` (`zz = stk.nat(2w)`, `powers` zeroed) ∘ `segPC`
(`buildPrecomputationWindowModPower2`); the continuation gets `AT` at `1795572` and the budget `b - cost0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

theorem bud_a {b b1 c1 c2 c3 : Nat} (h : c1 + c2 + c3 ≤ b) (h1 : b - c1 ≤ b1) : c2 ≤ b1 := by omega
theorem bud_b {b b1 b2 c1 c2 c3 : Nat} (h : c1 + c2 + c3 ≤ b) (h1 : b - c1 ≤ b1) (h2 : b1 - c2 ≤ b2) : c3 ≤ b2 := by
  omega
theorem bud_c {b b1 b2 b3 c1 c2 c3 : Nat} (h1 : b - c1 ≤ b1) (h2 : b1 - c2 ≤ b2) (h3 : b2 - c3 ≤ b3) :
    b - (c1 + c2 + c3) ≤ b3 := by omega
theorem lvl_ok {ℓ0 w : Nat} (hl16 : ℓ0 + 2 ^ 13 ≤ 2 ^ 16) (hW : w ≤ 128) :
    ℓ0 + 8 * w + StackNat.rnd (2 * w) + 2 ^ 12 ≤ 2 ^ 16 := by simp only [StackNat.rnd]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **from the entry to the table's return** -/
theorem entP {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract (LibExp.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibExp.program.link impl) mcE 4096 R)
    (hmv : MemmoveLive (LibExp.program.link impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hKk : 208 + kcP ≤ K)
    (hbud : cost0 sqC mlC (stLen s.mem st) lm ≤ b) (hr48 : ret < 2 ^ 48)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 yl)
    (h10 : s.regs 10 = BitVec.ofNat 64 lm) (h30 : s.regs 30 = BitVec.ofNat 64 ret)
    (KA : ∀ (s' : State) (L3 : List (Nat × Nat)) (b3 zzp bp : Nat), s'.pc = BitVec.ofNat 64 1795572 →
      s'.sp = BitVec.ofNat 64 sp → s'.regs 28 = BitVec.ofNat 64 g → s'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      s'.regs 18 = s.regs 18 → AT R L K g sp st zp zc xp xl xc yp yl lm ret s s'.mem L3 b3 zzp bp →
      b - cost0 sqC mlC (stLen s.mem st) lm ≤ b3 → ReachesRet (LibExp.program.link impl) ret0 s' Q) :
    ReachesRet (LibExp.program.link impl) ret0 s Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hlm2 := hP.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hl16 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst48 := hP.stk0.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hW1 : 1 ≤ W lm := by simp only [W]; omega
  refine ent impl R hgr hmc hwb ret0 Q b L K g sp st zp zc xp xl xc yp yl lm ret s hP
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hbud)) hr48 hpc h0 h2 h3 h4 h5 h6 h7 h8 h10 h30 ?_
  intro M L1 b1 hFc hFf hLF hrg hx hkf hlen hlc hc40 hnl hmem hsl hb1 hinv S hpcS hspS h3S h11S h18S h28S h29S hmS
  have hw := wc_rs hP hFf hLF hrg hx hkf hlen hlc hc40 hnl hmem hinv
  have hB1 : P2Pre.Hide (b - stackNatCost (stLen s.mem st) (8 * W lm) ≤ b1) := ⟨hb1⟩
  clear hb1 hFc hFf hLF hx hkf hlc hc40 hnl hmem hinv
  have hsl' := hsl
  obtain ⟨-, -, -, -, -, -, -, -, r496, r504, r512, r520, -, -, r552, -, -, -, -⟩ := hsl'
  refine segN hap hns hnf hsn haN ret0 Q b1 L1 g sp st lm xp xl xc M hal (by omega) hsp2 (by omega) hlm2 hlm
    (fun a k h1 h2 => hw.win_out hP (by omega) a k (by omega) h2) r496 r552 r504 r512 r520
    (by rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)) S hpcS hspS h3S h11S h28S
    hmS (fun S1 e1 e2 e3 => snPre hP hw (by omega) haN e1 e2 e3 (by omega) (by omega)
      (bud_a hbud hB1.h)) ?_
  intro S1 s' S2 c1 c2 c3 hpost hrg2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d30 d18 d28 d29 hFS2 hrgS2 q280 q112 q120
  have hS1N : S1.sp.toNat = sp := by rw [c1, BitVec.toNat_ofNat]; omega
  have hg1N : (S1.regs 28).toNat = g := by rw [c2, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  obtain ⟨L2, b2, hb2, hw2, hzs, hz0, -, -, hF2⟩ :=
    WC.stkNat hP hw (stk := stkN) (above := aboveN) (by omega) haN hS1N hg1N c3 hrg2 (n := 2 * W lm) (by omega) hpost
  have hw3 : WC R L K g sp st zp zc s.mem S2.mem L2 b2 (stLen s.mem st + 8 * W lm + StackNat.rnd (2 * W lm)) :=
    hw2.win hP hFS2 hrgS2 (nseg_ws sp K)
  have hB2 : P2Pre.Hide (b1 - stackNatCost (stLen s.mem st + 8 * W lm) (2 * W lm) ≤ b2) := ⟨hb2⟩
  clear hb2
  obtain ⟨hzN, hbu1⟩ := zz_post hw2.sok hw2.len (by omega) hz0
  -- the stack header is outside the window stores
  have hhd2 : ∀ a k, st ≤ a → a + k ≤ st + 24 → S2.mem.readLE a k = s'.mem.readLE a k := fun a k q1 q2 =>
    hFS2.readLE a k (hdr_nseg hstw hK q1 q2)
  have hbu2 : P2Pre.BU S2.mem st (stW s'.mem st + 8 * (stLen s.mem st + 8 * W lm)) (8 * (2 * W lm)) :=
    P2Pre.bu_hdr hbu1 (hhd2 _ _ (Nat.le_refl _) (by omega)) (hhd2 _ _ (by omega) (by omega))
      (hhd2 _ _ (by omega) (by omega))
  refine segPC hap hns hnfP hmv hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr hkT haT ret0 Q hP hw3 hKk
    (lvl_ok hl16 hW) (bud_b hbud hB1.h hB2.h) S2 d0 d1 d28 rfl d2 d3 d4 d5 d6 d7 d8 d9 d10 d30 ?_
  intro s'' L3 b3 bp e0 e1 e28 e29 e18 hw4 hb3 hpw hbs hbbu hkf3 hx3 hscr3 hF3
  have hlc3 := hw3.sok.2.2.2.2.2.1
  have hl3 := hw3.len
  have hl4 := hw4.len
  -- the slots
  have k2 : ∀ a k, SlotC sp a k → s'.mem.readLE a k = M.readLE a k := by
    intro a k ha
    have hin := slot_in ha
    refine hF2.readLE a k ?_
    have := hw.win_out hP (by omega) a k (by omega) hin.2
    rw [outside_append] at this ⊢; rw [outside_append]
    exact ⟨⟨this.1, slot_callee ha (by omega) haN⟩, this.2⟩
  have kS : ∀ a k, SlotC sp a k → S2.mem.readLE a k = s'.mem.readLE a k :=
    fun a k ha => hFS2.readLE a k (slot_n ha (by omega))
  have k3 : ∀ a k, sp - 8 ≤ a → a + k ≤ sp + 560 → Outside a k [(sp - (208 + kcP), sp - 8), (sp + 8, sp + 80)] →
      Outside a k [(sp + 320, sp + 416)] → s''.mem.readLE a k = S2.mem.readLE a k := by
    intro a k q1 q2 q3 q4
    refine hF3.readLE a k ?_
    have := hw3.win_out hP (by simp only [StackNat.rnd]; omega) a k (by omega) q2
    rw [outside_append] at this; rw [outside_append, outside_append]
    refine ⟨⟨this.1, ?_⟩, this.2⟩
    rw [show [(sp - (208 + kcP), sp - 8), (sp + 8, sp + 80), (sp + 320, sp + 416)] =
      [(sp - (208 + kcP), sp - 8), (sp + 8, sp + 80)] ++ [(sp + 320, sp + 416)] from rfl, outside_append]
    exact ⟨q3, q4⟩
  have hsl3 : ESl s''.mem sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st) :=
    ESl.keep (ESl.keep (ESl.keep hsl k2 (by omega)) kS (by omega))
      (fun a k ha => k3 a k (slot_in ha).1 (slot_in ha).2 (slot_callee ha (by omega) (by omega)) (slot_pw ha))
      (by omega)
  have hzr : ∀ o, o = 280 ∨ o = 112 ∨ o = 120 → s''.mem.readLE (sp + o) 8 = S2.mem.readLE (sp + o) 8 := by
    intro o ho
    refine k3 _ _ (by omega) (by omega) ?_ ?_ <;> simp only [outside_cons, outside_nil, and_true] <;> omega
  have hzh : Held R L2 (stW s'.mem st + 8 * (stLen s.mem st + 8 * W lm)) (8 * (2 * W lm)) := hzs.held
  refine KA s'' L3 b3 (stW s'.mem st + 8 * (stLen s.mem st + 8 * W lm)) bp e0 e1 e28 (e29.trans (d29.trans h29S))
    (e18.trans (d18.trans h18S)) ⟨hw4, hsl3, ?_, ?_, ?_, Scr.mono (Scr.mono hzs hFS2.accessible (LiveExt.refl R L2))
      hF3.accessible hx3, bu_after hbu2 hzh hkf3 (by rw [hl3, hl4]; omega), hpw, hbs, hbbu,
      scr_apart_bu hscr3 hbu2 hzh hlc3⟩ (bud_c hB1.h hB2.h hb3)
  · rw [hzr 280 (Or.inl rfl), q280, hzN]
  · rw [hzr 112 (Or.inr (Or.inl rfl)), q112]
  · rw [hzr 120 (Or.inr (Or.inr rfl)), q120]

end FvModexp.Arm64.P2W2
