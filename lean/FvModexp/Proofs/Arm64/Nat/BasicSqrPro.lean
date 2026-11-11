import FvModexp.Proofs.Arm64.Nat.BasicSqrClr
import FvModexp.Proofs.Arm64.Nat.BasicSqrEnv
import FvModexp.Proofs.Common.DivmcLsl
import FvModexp.Proofs.Arm64.Nat.BasicSqrSmall

/-!
# `basicSqr` (arm64): the large path's prologue — `defer stk.restore(stk.save())`, `t := stk.nat(2n)` (natmul.go:119-120)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.BasicSqr

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0x80

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s P : State) : Prop where
  pc : P.pc = BitVec.ofNat 64 callNat
  sp : P.sp = s.sp - 208#64
  r28 : P.regs 28 = s.regs 28
  r29 : P.regs 29 = s.sp - 216#64
  r18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (2 * xl)
  fr : MemFrame s.mem P.mem [(s.sp.toNat - 216, s.sp.toNat - 200), (s.sp.toNat - 89, s.sp.toNat - 88),
    (s.sp.toNat - 56, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 64)]
  reg : P.mem.regions = s.mem.regions
  lr : P.mem.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat
  fp : P.mem.readLE (s.sp.toNat - 216) 8 = (s.regs 29).toNat
  kk : P.mem.readLE (s.sp.toNat - 56) 8 = 2 * xl
  dfn : P.mem.readLE (s.sp.toNat - 40) 8 = segAddr LibBasicSqr.program (fn ++ ".deferwrap1")
  dst : P.mem.readLE (s.sp.toNat - 32) 8 = st
  dn : P.mem.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : P.mem.readLE (s.sp.toNat + 16) 8 = zp
  s2 : P.mem.readLE (s.sp.toNat + 24) 8 = zl
  s3 : P.mem.readLE (s.sp.toNat + 32) 8 = zc
  s4 : P.mem.readLE (s.sp.toNat + 40) 8 = xp
  s5 : P.mem.readLE (s.sp.toNat + 48) 8 = xl
  s6 : P.mem.readLE (s.sp.toNat + 56) 8 = xc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
/-- after `(*stack).nat` returned (state `S2`): the three result spills, up to `clear(t)` -/
theorem pro3 (impl : List Segment) (R : RtInv) (stkSN abSN : Nat) (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (hmc : MemclrNoHeapPointersLive (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (P : State) (hP : AtNat R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s P)
    (S2 : State) (hpc2 : S2.pc = BitVec.ofNat 64 (callNat + 4)) (hsp2 : S2.sp = s.sp - 208#64)
    (h28 : S2.regs 28 = s.regs 28) (h29 : S2.regs 29 = s.sp - 216#64) (h18 : S2.regs 18 = s.regs 18)
    (hr0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st.toNat + 8 * stLen s.mem st.toNat))
    (hr1 : S2.regs 1 = BitVec.ofNat 64 (2 * xl.toNat)) (hr2 : S2.regs 2 = BitVec.ofNat 64 (2 * xl.toNat))
    (L1 : List (Nat × Nat)) (b1 : Nat) (hext : LiveExt R L L1)
    (hbud : b - ExpHyp.stackNatCost (stLen s.mem st.toNat) (2 * xl.toNat) ≤ b1)
    (hinv2 : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S2.mem)) (hok : StkOK S2.mem R L1 st.toNat)
    (hlen2 : stLen S2.mem st.toNat = stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4)
    (hsame : stLen s.mem st.toNat + 2 * xl.toNat ≤ stCap s.mem st.toNat →
      stW S2.mem st.toNat = stW s.mem st.toNat ∧ stCap S2.mem st.toNat = stCap s.mem st.toNat)
    (hgrow : stCap s.mem st.toNat < stLen s.mem st.toNat + 2 * xl.toNat →
      InRanges (stW S2.mem st.toNat) (8 * stCap S2.mem st.toNat) R.rt ∧
        ApartAll (stW S2.mem st.toNat) (8 * stCap S2.mem st.toNat) L)
    (hF2 : MemFrame P.mem S2.mem (R.rt ++ [(s.sp.toNat - 208 - stkSN, s.sp.toNat - 216),
      (s.sp.toNat - 200, s.sp.toNat - 208 + abSN)] ++ stkWs s.mem st.toNat))
    (hLF2 : LiveFrame P.mem S2.mem L (stkWs s.mem st.toNat)) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S2 fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  obtain ⟨-, -, -, -, -, -, -, hF, -, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := hP
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hpre.ce
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hfw := hpre.stfw; simp only [win, outside_cons, outside_nil, and_true, freeP, freeN] at hfw
  have hlc := hpre.stok.2.2.2.2.2.1
  have hst48 := hpre.stok.2.2.2.1
  have hPs : ∀ a n, (a + n ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 64 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hE := env_of (P := P.mem) (S2 := S2.mem) hpre hbig (fun k hk => hPs _ _ (by omega))
    (fun a n v => hF.accessible a n v) hext
    (by simp only [stLen] at hbud ⊢; rw [hPs _ _ (by omega)]; exact hbud) hok
    (by simp only [stLen] at hlen2 ⊢; rw [hlen2, hPs _ _ (by omega)])
    (by simp only [stLen, stW, stCap] at hsame ⊢
        rw [hPs (st.toNat + 8) _ (by omega), hPs (st.toNat + 16) _ (by omega), hPs st.toNat _ (by omega)]; exact hsame)
    (by simp only [stLen, stW, stCap] at hgrow ⊢
        rw [hPs (st.toNat + 8) _ (by omega), hPs (st.toNat + 16) _ (by omega)]; exact hgrow) (fun a n v => hF2.accessible a n v)
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hx0 := hl.x0
  -- reads of `S2.mem` in the frame record
  have k2 : ∀ a, (s.sp.toNat - 216 ≤ a ∧ a + 8 ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 112 ≤ a ∧ a + 8 ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → S2.mem.readLE a 8 = P.mem.readLE a 8 := by
    intro a ha
    refine hF2.readLE _ _ ?_
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega⟩
  have kst : ∀ k, k + 8 ≤ 24 → S2.mem.readLE (st.toNat + k) 8 = S2.mem.readLE (st.toNat + k) 8 := fun _ _ => rfl
  have q1 := (k2 _ (by omega)).trans p1
  have q2 := (k2 _ (by omega)).trans p2
  have hr1' : (S2.regs 1).toNat = 2 * xl.toNat := by rw [hr1]; simp only [BitVec.toNat_ofNat]; omega
  have hnz : S2.regs 1 ≠ 0#64 := by intro h; rw [h] at hr1'; simp at hr1'; omega
  have hlsl := lsl3_ofNat (2 * xl.toNat) (by have := hpre.stlen; simp only [stLen] at this; omega)
  have ht48 := hE.scr.b48
  janus_run [hr0, hr1, hr2] until [callClr]
  generalize hMq : ((S2.mem.writeLE (s.sp.toNat - 48) 8 (stW S2.mem st.toNat + 8 * stLen s.mem st.toNat)).writeLE
      (s.sp.toNat - 80) 8 (2 * xl.toNat)).writeLE (s.sp.toNat - 88) 8 (2 * xl.toNat) = Mq
  have kq : ∀ a n, (a + n ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 72 ≤ a) → (a + n ≤ s.sp.toNat - 48 ∨ s.sp.toNat - 40 ≤ a) →
      Mq.readLE a n = S2.mem.readLE a n := by
    intro a n h1 h2
    rw [← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hst : MemFrame S2.mem Mq [(s.sp.toNat - 88, s.sp.toNat - 72), (s.sp.toNat - 48, s.sp.toNat - 40)] :=
    ⟨fun a n h => by simp only [outside_cons, outside_nil, and_true] at h; exact kq a n h.1 h.2,
     fun a n v => by rw [← hMq]; simp only [Memory.accessible_writeLE]⟩
  have hsw' := hl.sw
  have ks : ∀ a, (s.sp.toNat - 216 ≤ a ∧ a + 8 ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 72 ≤ a ∧ a + 8 ≤ s.sp.toNat - 48) ∨
      (s.sp.toNat - 40 ≤ a ∧ a + 8 ≤ s.sp.toNat - 8) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) →
      Mq.readLE a 8 = P.mem.readLE a 8 := fun a ha => by
    rw [kq a 8 (by omega) (by omega), k2 a (by omega)]
  have kst : ∀ k, k + 8 ≤ 24 → Mq.readLE (st.toNat + k) 8 = S2.mem.readLE (st.toNat + k) 8 :=
    fun k hk => kq _ _ (by omega) (by omega)
  refine clr impl R hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s _ L1 b1 _ _ hE hl4 hl48 _ ?_ ?_ ?_ ?_ ?_ ?_ ?r1
    ⟨(ks _ (by omega)).trans p1, (ks _ (by omega)).trans p2, ?tl, ?tc, (ks _ (by omega)).trans p3, ?tp,
      (ks _ (by omega)).trans p4, (ks _ (by omega)).trans p5, (ks _ (by omega)).trans p6, (ks _ (by omega)).trans p7,
      (ks _ (by omega)).trans p8, (ks _ (by omega)).trans p9, (ks _ (by omega)).trans p10,
      (ks _ (by omega)).trans p11, (ks _ (by omega)).trans p12, (ks _ (by omega)).trans p13,
      kst 0 (by omega), (kst 8 (by omega)).trans hlen2, kst 16 (by omega), ?xs, ?fr, ?lf, ?inv⟩
  case r1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hr1, hlsl]; congr 1; omega
  case tl => rw [← hMq, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  case tc =>
    rw [← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case tp =>
    rw [← hMq, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case xs =>
    intro a n h1 h2
    have hxw := hl.xw
    have hfr := hpre.free.2; have hsx := hpre.stx
    simp only [freeP, freeN] at hfr
    unfold Apart at hfr hsx
    rw [kq a n (by omega) (by omega), Held.readLE2 (hpre.xh.sub h1 h2) hF2 hLF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega), hPs a n (by omega)]
  case fr =>
    refine (mfTrans hF (mfTrans hF2 hst)).mono fun a n ho => ?_
    simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨⟨h1, h2, h3⟩, h4, h5⟩, h6, h7⟩ := ho
    refine ⟨?_, ⟨⟨h1, ?_, ?_⟩, h6, h7⟩, ?_, ?_⟩
    all_goals clear h4 h5 h6 h7
    all_goals omega
  case lf =>
    refine ⟨fun a n hin hws => ?_⟩
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at hws
    obtain ⟨⟨h4, h5⟩, h6, h7⟩ := hws
    have hw0 : a + n ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; clear h4 h5 h6 h7; omega
    rw [kq a n (by clear h4 h5 h6 h7; omega) (by clear h4 h5 h6 h7; omega),
      hLF2.readLE a n hin (by simp only [stkWs, outside_cons, outside_nil, and_true]; exact ⟨h6, h7⟩),
      hPs a n (by clear h4 h5 h6 h7; omega)]
  case inv =>
    rw [← hMq]
    refine inv_store_out (inv_store_out (inv_store_out hinv2 ?_) ?_) ?_ <;> exact hout.of_sub (by omega) (by omega)
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : ExpHyp.StackNatHyp impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (hmc : MemclrNoHeapPointersLive (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (P : State) (hP : AtNat R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s P)
    (hinvP : R.inv b L (s.regs 28).toNat (view R.rt L P.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) P fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments [ExpHyp.fnStackNat]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hSN' := fun b L => Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1)
    (noExit_restrict hap [ExpHyp.fnStackNat]) hc
  clear hc
  obtain ⟨hpc, hsp, h28, h29, h18, r0, r1, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := hP
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  simp only [win, outside_cons, outside_nil, and_true] at hLs
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 64 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hPacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_win hdl hreg hro (hF.widen R.rt) hw (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega)
  have hgP : P.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hrd _ _ (by unfold Apart at hga; omega)
  have hstok := hpre.stok
  have hstO : StkOK P.mem R L st.toNat := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hstok
    simp only [StkOK, stW, stLen, stCap] at a5 a6 a7 ⊢
    rw [hrd st.toNat 8 (by omega), hrd (st.toNat + 8) 8 (by omega), hrd (st.toNat + 16) 8 (by omega), hPacc]
    refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
    intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hPacc]; exact b3, b4⟩
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9⟩ := hpre.sv
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 208 - stkSN ∨ s.sp.toNat - 208 + abSN ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hstO
  have q2' : InRanges st.toNat 24 L ∨ Outside st.toNat 24 R.rt := q2
  simp only [NatLive, stW, stCap, stLen] at q5 q6 q7
  have hlen := hpre.stlen
  have r0' : P.regs 0 = st := by rw [r0]; simp
  have e208 : (s.sp - 208#64).toNat = s.sp.toNat - 208 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have eW : ExpHyp.stW P.mem st.toNat = stW s.mem st.toNat := hrd _ _ (by omega)
  have eL : ExpHyp.stLen P.mem st.toNat = stLen s.mem st.toNat := hrd _ _ (by omega)
  have eC : ExpHyp.stCap P.mem st.toNat = stCap s.mem st.toNat := hrd _ _ (by omega)
  have hn2 : 2 * xl.toNat % 18446744073709551616 = 2 * xl.toNat := Nat.mod_eq_of_lt (by simp only [stLen] at hlen; omega)
  have hcost := hpre.cost
  have hstarr := hpre.starr
  simp only [stW, stCap, stLen] at hlen hcost hstarr
  by_cases hc0 : 0 < s.mem.readLE (st.toNat + 16) 8
  · have hnl := hpre.stok.2.2.2.2.1
    simp only [NatLive, stW, stCap] at hnl
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc0
    obtain ⟨a5, a6⟩ := hstarr hc0
    simp only [win, outside_cons, outside_nil, and_true] at a5
    unfold Apart at a6
    have a2' : InRanges (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) L ∨
      Outside (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) R.rt := a2
    janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, hn2] until [callNat + 4] calls [hSN' b L]
    rename_i hpc' hsp' h28' h29' h18' hr0 hr1 hr2 L1 b1 hext hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 _ hsame hgrow hF2 hLF2
    refine pro3 impl R stkSN abSN hk1 hk2 hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hl4 hl48 P
      ⟨hpc, hsp, h28, h29, h18, r0, r1, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ s'
      ?qpc ?qsp ?q28 ?q29 ?q18 ?q0 ?q1 ?q2 L1 b1 hext hbud hinv2
      ⟨k1, k2, by rw [hF2.accessible, hF.accessible]; exact k3, by omega, k5, k6, k7⟩ hlen2 hsame hgrow ?F2 ?LF2
    case F2 =>
      simp only [winA, ExpHyp.stWs, e208, eW, eL, eC, show s.sp.toNat - 208 - 8 = s.sp.toNat - 216 by omega,
        show s.sp.toNat - 208 + 8 = s.sp.toNat - 200 by omega] at hF2
      exact hF2
    case LF2 =>
      simp only [ExpHyp.stWs, eW, eL, eC] at hLF2
      exact hLF2
    case q0 => rw [hr0]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r0', eL]
    case q1 => rw [hr1]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q2 => rw [hr2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q28 => rw [h28']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case q29 => rw [h29']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
    case q18 => rw [h18']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
    case qsp => rw [hsp']
    case qpc => rw [hpc']; janus_simp
  · janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, hn2] until [callNat + 4] calls [hSN' b L]
    rename_i hpc' hsp' h28' h29' h18' hr0 hr1 hr2 L1 b1 hext hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 _ hsame hgrow hF2 hLF2
    refine pro3 impl R stkSN abSN hk1 hk2 hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hl4 hl48 P
      ⟨hpc, hsp, h28, h29, h18, r0, r1, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ s'
      ?qpc ?qsp ?q28 ?q29 ?q18 ?q0 ?q1 ?q2 L1 b1 hext hbud hinv2
      ⟨k1, k2, by rw [hF2.accessible, hF.accessible]; exact k3, by omega, k5, k6, k7⟩ hlen2 hsame hgrow ?F2 ?LF2
    case F2 =>
      simp only [winA, ExpHyp.stWs, e208, eW, eL, eC, show s.sp.toNat - 208 - 8 = s.sp.toNat - 216 by omega,
        show s.sp.toNat - 208 + 8 = s.sp.toNat - 200 by omega] at hF2
      exact hF2
    case LF2 =>
      simp only [ExpHyp.stWs, eW, eL, eC] at hLF2
      exact hLF2
    case q0 => rw [hr0]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r0', eL]
    case q1 => rw [hr1]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q2 => rw [hr2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, r1, BitVec.toNat_ofNat, hn2]
    case q28 => rw [h28']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case q29 => rw [h29']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
    case q18 => rw [h18']; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
    case qsp => rw [hsp']
    case qpc => rw [hpc']; janus_simp

end FvModexp.Arm64.BasicSqr
