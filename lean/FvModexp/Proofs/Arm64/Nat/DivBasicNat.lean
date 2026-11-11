import FvModexp.Proofs.Arm64.Nat.DivBasicPro
import FvModexp.Proofs.Arm64.Nat.Callees2

/-!
# `divBasic` (arm64): the call `qhatv := stk.nat(n + 1)` (natdiv.go:651)

`pro2`: from `AtNat` (state `P` at `CALL (*stack).nat`) through the call (premise `StackNatHyp`, as in divmc's
`BasicSqr.pro2`), to the return point with the post facts `AfterNat` handed to a continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

/-- the facts right after `(*stack).nat` returned (state `S2`; `P` the call state) -/
structure AfterNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st vl : Nat) (s P S2 : State) (stkSN abSN : Nat)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  pc : S2.pc = BitVec.ofNat 64 (callNat + 4)
  sp : S2.sp = s.sp - 240#64
  r28 : S2.regs 28 = s.regs 28
  r29 : S2.regs 29 = s.sp - 248#64
  r18 : S2.regs 18 = s.regs 18
  r0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st + 8 * stLen s.mem st)
  r1 : S2.regs 1 = BitVec.ofNat 64 (vl + 1)
  r2 : S2.regs 2 = BitVec.ofNat 64 (vl + 1)
  ext : LiveExt R L L1
  bud : b - ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S2.mem)
  ok : StkOK S2.mem R L1 st
  len : stLen S2.mem st = stLen s.mem st + (vl + 1 + 3) / 4 * 4
  same : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st →
    stW S2.mem st = stW s.mem st ∧ stCap S2.mem st = stCap s.mem st
  grow : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 →
    InRanges (stW S2.mem st) (8 * stCap S2.mem st) R.rt ∧ ApartAll (stW S2.mem st) (8 * stCap S2.mem st) L
  F2 : MemFrame P.mem S2.mem (R.rt ++ [(s.sp.toNat - 240 - stkSN, s.sp.toNat - 248),
    (s.sp.toNat - 232, s.sp.toNat - 240 + abSN)] ++ stkWs s.mem st)
  LF2 : LiveFrame P.mem S2.mem L (stkWs s.mem st)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : ExpHyp.StackNatHyp impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : BitVec 64) (s : State)
    (hpre : Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s)
    (P : State) (hP : AtNat R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s P)
    (hinvP : R.inv b L (s.regs 28).toNat (view R.rt L P.mem)) (Q : State → Prop)
    (k : ∀ S2 L1 b1, AfterNat R b L st.toNat vl.toNat s P S2 stkSN abSN L1 b1 →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S2 Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) P Q := by
  have hc : CodeIn ((Extracted.program.onlySegments [ExpHyp.fnStackNat]).link impl) (LibDivBasic.program.link impl) := by
    rw [LibDivBasic.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hSN' := fun b L => Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1)
    (noExit_restrict hap [ExpHyp.fnStackNat]) hc
  clear hc
  obtain ⟨hpc, hsp, h28, h29, h18, r0, r1, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14,
    p15, p16⟩ := hP
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  simp only [win, outside_cons, outside_nil, and_true] at hLs
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 248 ∨ s.sp.toNat + 88 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
  have hPacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_win hdl hreg hro (hF.widen R.rt) hw (by
      intro r hr; simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  have hgP : P.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hrd _ _ (by unfold Apart at hga; omega)
  have hwbP : P.mem.accessible StackNat.wbA 4 false = true := by rw [hPacc]; exact hpre.wbacc
  have hwbA := hpre.wbap
  have hstfree := hpre.stfree
  have hstok := hpre.stok
  have hstO : StkOK P.mem R L st.toNat := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hstok
    simp only [StkOK, stW, stLen, stCap] at a5 a6 a7 ⊢
    rw [hrd st.toNat 8 (by omega), hrd (st.toNat + 8) 8 (by omega), hrd (st.toNat + 16) 8 (by omega), hPacc]
    refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
    intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hPacc]; exact b3, b4⟩
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9⟩ := hpre.sv
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 240 - stkSN ∨ s.sp.toNat - 240 + abSN ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hstO
  have q2' : InRanges st.toNat 24 L ∨ Outside st.toNat 24 R.rt := q2
  simp only [NatLive, stW, stCap, stLen] at q5 q6 q7
  have hlen := hpre.stlen
  have r0' : P.regs 0 = st := by rw [r0]; simp
  have e240 : (s.sp - 240#64).toNat = s.sp.toNat - 240 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have eW : stW P.mem st.toNat = stW s.mem st.toNat := hrd _ _ (by omega)
  have eL : stLen P.mem st.toNat = stLen s.mem st.toNat := hrd _ _ (by omega)
  have eC : stCap P.mem st.toNat = stCap s.mem st.toNat := hrd _ _ (by omega)
  have hn2 : (vl.toNat + 1) % 18446744073709551616 = vl.toNat + 1 := Nat.mod_eq_of_lt (by simp only [stLen] at hlen; omega)
  have hcost := hpre.cost
  have hstarr := hpre.starr
  simp only [stW, stCap, stLen, freeP, freeN] at hlen hcost hstarr hstfree
  unfold Apart at hwbA hstfree
  by_cases hc0 : 0 < s.mem.readLE (st.toNat + 16) 8
  · have hnl := hpre.stok.2.2.2.2.1
    simp only [NatLive, stW, stCap] at hnl
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc0
    obtain ⟨a5, a6⟩ := hstarr hc0
    simp only [win, outside_cons, outside_nil, and_true] at a5
    unfold Apart at a6
    have a2' : InRanges (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) L ∨
      Outside (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) R.rt := a2
    janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, hn2] until [callNat + 4]
      calls [hSN' b L]
    rename_i hpc' hsp' h28' h29' h18' hr1 hr2 L1 b1 hext hr0 hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame hgrow hF2 hLF2
    refine k s' L1 b1 ⟨?qpc, ?qsp, ?q28, ?q29, ?q18, ?q0, ?q1, ?q2, hext, by simpa using hbud, hinv2,
      ⟨k1, k2, by rw [hF2.accessible, hF.accessible]; exact k3, by omega, k5, k6, k7⟩, ?qlen, ?qsame, ?qgrow, ?F2, ?LF2⟩
    case qlen => rw [hlen2]
    case qsame => intro h; exact hsame h
    case qgrow => intro h; exact hgrow h
    case F2 =>
      simp only [winA, ExpHyp.stWs, stkWs, e240, eW, eL, eC, show s.sp.toNat - 240 - 8 = s.sp.toNat - 248 by omega,
        show s.sp.toNat - 240 + 8 = s.sp.toNat - 232 by omega] at hF2
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
  · janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, hn2] until [callNat + 4]
      calls [hSN' b L]
    rename_i hpc' hsp' h28' h29' h18' hr1 hr2 L1 b1 hext hr0 hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame hgrow hF2 hLF2
    refine k s' L1 b1 ⟨?qpc, ?qsp, ?q28, ?q29, ?q18, ?q0, ?q1, ?q2, hext, by simpa using hbud, hinv2,
      ⟨k1, k2, by rw [hF2.accessible, hF.accessible]; exact k3, by omega, k5, k6, k7⟩, ?qlen, ?qsame, ?qgrow, ?F2, ?LF2⟩
    case qlen => rw [hlen2]
    case qsame => intro h; exact hsame h
    case qgrow => intro h; exact hgrow h
    case F2 =>
      simp only [winA, ExpHyp.stWs, stkWs, e240, eW, eL, eC, show s.sp.toNat - 240 - 8 = s.sp.toNat - 248 by omega,
        show s.sp.toNat - 240 + 8 = s.sp.toNat - 232 by omega] at hF2
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

end FvModexp.Arm64.DivBasic
