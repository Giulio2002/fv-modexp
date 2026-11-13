import FvModexp.Proofs.Arm64.NatQ.DivLargeRel
import FvModexp.Proofs.Arm64.Nat.Callees2
import FvModexp.Proofs.Arm64.Nat.StackNatXDefs

set_option autoImplicit false
/-! (Q-form copy of Arm64/Nat/DivLargeNat.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): the call `qhatv := stk.nat(n + 1)` (natdiv.go:651)

`pro2`: from `AtNat` (state `P` at `CALL (*stack).nat`) through the call (premise `StackNatHyp`, as in divmc's
`BasicSqr.pro2`), to the return point with the post facts `AfterNat` handed to a continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : StackNatX.HypQ impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : BitVec 64) (s : State)
    (hpre : Pre R b H L c zp.toNat zc.toNat st.toNat up.toNat uc.toNat ip.toNat il.toNat vp.toNat vl.toNat s)
    (P : State) (hP : AtNat st.toNat up.toNat uc.toNat ip.toNat il.toNat ic.toNat vp.toNat vl.toNat vc.toNat zp.toNat
      zc.toNat s P)
    (hinvP : R.inv b L (s.regs 28).toNat (view R.rt L P.mem)) (Q : State → Prop)
    (k : ∀ S2 L1 b1, AfterNat R b H L st.toNat vl.toNat s P S2 stkSN abSN L1 b1 →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) S2 Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) P Q := by
  have hc : CodeIn ((Extracted.program.onlySegments [ExpHyp.fnStackNat]).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hSN' := fun H b L => Ensures.toSummaryRegs2 (fun a0 a1 => hSN H b L a0 a1)
    (noExit_restrict hap [ExpHyp.fnStackNat]) hc
  clear hc
  obtain ⟨hpc, hsp, h28, h29, h18, r0, r1, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14,
    p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27⟩ := hP
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  simp only [win, outside_cons, outside_nil, and_true] at hLs
  obtain ⟨hstok, hsw, hsg, hstarr⟩ := hpre.sti
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 312 ∨ s.sp.toNat + 112 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
  have hPacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_win hdl hreg hro (hF.widen R.rt) hw (by
      intro r hr; simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  have hgP : P.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hrd _ _ (by unfold Apart at hga; omega)
  have hwbP : P.mem.accessible StackNat.wbA 4 false = true := by rw [hPacc]; exact hpre.gl.2.2.2.2.2.2.2.2.2.2.1
  have hwbA := hpre.wbap
  have hstO : StkOK P.mem R L st.toNat := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hstok
    simp only [StkOK, stW, stLen, stCap] at a5 a6 a7 ⊢
    rw [hrd st.toNat 8 (by omega), hrd (st.toNat + 8) 8 (by omega), hrd (st.toNat + 16) 8 (by omega), hPacc]
    refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
    intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hPacc]; exact b3, b4⟩
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9⟩ := hpre.sv
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 304 - stkSN ∨ s.sp.toNat - 304 + abSN ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hstO
  have q2' : InRanges st.toNat 24 L ∨ Outside st.toNat 24 R.rt := q2
  simp only [NatLive, stW, stCap, stLen] at q5 q6 q7
  have hlen := hpre.stl
  have hvil := hpre.vil
  have hil9 := hpre.il9
  have r0' : P.regs 0 = st := by rw [r0]; simp
  have e240 : (s.sp - 304#64).toNat = s.sp.toNat - 304 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have eW : stW P.mem st.toNat = stW s.mem st.toNat := hrd _ _ (by omega)
  have eL : stLen P.mem st.toNat = stLen s.mem st.toNat := hrd _ _ (by omega)
  have eC : stCap P.mem st.toNat = stCap s.mem st.toNat := hrd _ _ (by omega)
  have hn2 : vl.toNat % 18446744073709551616 = vl.toNat := Nat.mod_eq_of_lt (by omega)
  have hcP : stkR H P.mem st.toNat ≤ b := by rw [stkR_congr eC]; have := hpre.cost; omega
  have hcost : stLen s.mem st.toNat + vl.toNat + 3 ≤ H := by have := hpre.lvH; omega
  have hstfree : Apart st.toNat 24 (stW s.mem st.toNat + 8 * stLen s.mem st.toNat) (8 * (stCap s.mem st.toNat - stLen s.mem st.toNat)) := hpre.hf
  simp only [stW, stCap, stLen] at hlen hcost hstarr hstfree
  unfold Apart at hwbA hstfree
  by_cases hc0 : 0 < s.mem.readLE (st.toNat + 16) 8
  · have hnl := hstok.2.2.2.2.1
    simp only [NatLive, stW, stCap] at hnl
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc0
    obtain ⟨a5, a6⟩ := hstarr hc0
    simp only [win, outside_cons, outside_nil, and_true] at a5
    unfold Apart at a6
    have a2' : InRanges (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) L ∨
      Outside (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) R.rt := a2
    janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, hn2] until [callNat + 4]
      calls [hSN' H b L]
    rename_i hpc' hsp' h28' h29' h18' hr1 hr2 L1 b1 hext hr0 hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame hgrow hF2 hLF2 hmem
    refine k s' L1 b1 ⟨?qpc, ?qsp, ?q28, ?q29, ?q18, ?q0, ?q1, ?q2, hext, by rw [stkR_congr eC] at hbud; exact hbud, hinv2,
      ⟨k1, k2, by rw [hF2.accessible, hF.accessible]; exact k3, by omega, k5, k6, k7⟩, ?qlen, ?qsame, ?qgrow, ?F2, ?LF2, ?qreg, ?qmem⟩
    case qreg => rw [hrg1, hreg]
    case qmem => intro h; exact hmem h
    case qlen => rw [hlen2]
    case qsame => intro h; exact hsame h
    case qgrow => intro h; exact hgrow h
    case F2 =>
      simp only [winA, ExpHyp.stWs, stkWs, e240, eW, eL, eC, show s.sp.toNat - 304 - 8 = s.sp.toNat - 312 by omega,
        show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega] at hF2
      exact hF2
    case LF2 =>
      simp only [ExpHyp.stWs, stkWs, eW, eL, eC] at hLF2
      exact hLF2
    case q0 => rw [hr0 (by omega)]
    case q1 => rw [hr1]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q2 => rw [hr2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q28 => rw [h28']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case q29 => rw [h29']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
    case q18 => rw [h18']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
    case qsp => rw [hsp']
    case qpc => rw [hpc']; janus_simp
  · janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, hn2] until [callNat + 4]
      calls [hSN' H b L]
    rename_i hpc' hsp' h28' h29' h18' hr1 hr2 L1 b1 hext hr0 hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame hgrow hF2 hLF2 hmem
    refine k s' L1 b1 ⟨?qpc, ?qsp, ?q28, ?q29, ?q18, ?q0, ?q1, ?q2, hext, by rw [stkR_congr eC] at hbud; exact hbud, hinv2,
      ⟨k1, k2, by rw [hF2.accessible, hF.accessible]; exact k3, by omega, k5, k6, k7⟩, ?qlen, ?qsame, ?qgrow, ?F2, ?LF2, ?qreg, ?qmem⟩
    case qreg => rw [hrg1, hreg]
    case qmem => intro h; exact hmem h
    case qlen => rw [hlen2]
    case qsame => intro h; exact hsame h
    case qgrow => intro h; exact hgrow h
    case F2 =>
      simp only [winA, ExpHyp.stWs, stkWs, e240, eW, eL, eC, show s.sp.toNat - 304 - 8 = s.sp.toNat - 312 by omega,
        show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega] at hF2
      exact hF2
    case LF2 =>
      simp only [ExpHyp.stWs, stkWs, eW, eL, eC] at hLF2
      exact hLF2
    case q0 => rw [hr0 (by omega)]
    case q1 => rw [hr1]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q2 => rw [hr2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q28 => rw [h28']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case q29 => rw [h29']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
    case q18 => rw [h18']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
    case qsp => rw [hsp']
    case qpc => rw [hpc']; janus_simp

end FvModexp.Arm64.Q.DivLarge
