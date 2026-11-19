import FvModexp.Proofs.Amd64.Nat.DivLargeDBP
import FvModexp.Proofs.Common.DivLargeMath

set_option autoImplicit false

/-!
# `divLarge` (amd64): the precondition of `q.divRecursiveStep(stk, u, v, 0)` at its call (pure)

`n ≥ divRecursiveThreshold`: `divRecursive` (inlined, natdiv.go:740) clears `q` (`memclr`) and calls
`divRecursiveStep(stk, u, v, 0)`. At the callee entry `X` (`RSP = entry RSP - 312`, window `40960 / 96`, i.e. exactly
`[RSP - 41272, RSP - 216)`): memory = `AtJ`'s with `scrB` slots, the stack args / return address and `q` written.
`DrsPre`'s value condition `2·U' < 2^(64(n + m + 1))` holds since `U' = U·2^sh`, `sh ≤ 63`, `U < 2^(64·len uIn)`.
Port of `Arm64/Nat/DivLargeDRP.lean`; `Ensures.toSummaryRegs8D` = the 8-register-argument summary form (`R10` = depth).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivLarge

-- adapted from asm's `FvModexp.Amd64.DivW.Ensures.toSummaryRegs8` (Proofs/Amd64/Nat/DivWDefs.lean), copied to keep the
-- divLarge chain free of the `divW` modules
theorem Ensures.toSummaryRegs8D {p0 P : Amd64.Program} {entry : Nat}
    {pre : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State → Prop}
    {post : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State →
      State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7]
      (pre a0 a1 a2 a3 a4 a5 a6 a7) (post a0 a1 a2 a3 a4 a5 a6 a7))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧ s.df = false ∧
        pre (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        post (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) s s') := by
  intro s hpc ⟨hret, hz, hdf, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9)
    (s.regs 10)) hx (by simp [numIntRegs]) hc s hpc ⟨hret, hz, by simp [ArgsFrom64, argReg, intArgRegs], hdf, hpre⟩

/-- the threshold globals and the write-barrier flag survive a frame that keeps them
(adapted from fv-modexp top's arm64 `globals_frame'`, Proofs/Arm64/Nat/DivLargeDRP.lean) -/
theorem globals_frame' {R : RtInv} {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' (R.rt ++ ws)) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt.of_sub (by omega) (by omega), hg.of_sub (by omega) (by omega)⟩)
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the writes since the entry (and `q`'s array) are apart from the threshold globals (pure) -/
theorem ga_ws {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) :
    Outside RunIface.gA 32 (win s 41272 112 ++ wsL zp zc up uc vl t ++ stkWs s.mem st ++ scrB s) ∧
      Outside RunIface.gA 32 R.rt ∧
      Apart RunIface.gA 32 (w1 + 8 * (stLen s.mem st + StackNat.rnd vl)) (8 * (c1 - (stLen s.mem st + StackNat.rnd vl))) := by
  have hpre := hE.pre
  obtain ⟨-, -, -, -, -, -, -, -, hrt, hw, -⟩ := hpre.gl
  obtain ⟨hz, hu, hs, hf⟩ := hpre.ga
  simp only [win, outside_cons, outside_nil, and_true] at hw
  have hlc := hpre.sti.1.2.2.2.2.2.1
  have hc1 := hE.c1len
  refine ⟨?_, hrt, ?_⟩
  · rw [outside_append, outside_append, outside_append]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [win, outside_cons, outside_nil, and_true]; omega
    · refine outside_wsL ?_ (fun h => by have := hz h; unfold Apart at this; omega)
        (fun h => by have := hu h; unfold Apart at this; omega)
      rcases hE.scr.loc with ⟨-, h1, h2⟩ | ⟨hin, -⟩
      · unfold Apart at hf; omega
      · have := outside_of_inRanges hrt hin; omega
    · unfold Apart at hs hf
      simp only [stkWs, outside_cons, outside_nil, and_true]; omega
    · simp only [scrB, outside_cons, outside_nil, and_true]; omega
  · rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · unfold Apart at hf ⊢; omega
    · have := outside_of_inRanges hrt hin; unfold Apart; omega

/-- `DataLoaded` at a state whose memory is `Mem`'s with further writes `ws2` inside accessible ranges (pure) -/
theorem dl_at2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    (hM : Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk M)
    {ws2 : List (Nat × Nat)} (hF : MemFrame M M' (R.rt ++ ws2))
    (hws2 : ∀ r ∈ ws2, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true) (hreg : M'.regions = s.mem.regions) :
    Extracted.program.DataLoaded M' := by
  have hpre := hE.pre
  have hl := hE.lay
  have hsp0 := hl.sp0
  have hd : Extracted.program.DataLoaded s.mem := hpre.ce.2.2.2.1
  have hro : RoOut R := hpre.ce.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  refine dataLoaded_frame64 hd hreg hro ((mfTrans hM.fr hF).mono fun a n ho => ?_) (ws := win s 41272 112 ++
    wsL zp zc up uc vl t ++ stkWs s.mem st ++ ws2) ?_
  · simp only [outside_append] at ho ⊢
    obtain ⟨h0, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := ho
    exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h0, h4⟩
  · intro r hr hlt
    rw [List.mem_append, List.mem_append, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · simp only [wsL, List.mem_cons, List.mem_append] at hr
      rcases hr with rfl | hr | hr
      · simp only [Nat.add_sub_cancel_left]; exact hE.scr.acc
      · unfold ar at hr; split at hr
        · next hc =>
          simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]
          exact (hpre.zo.2.1 hc).2.2.1
        · simp at hr
      · unfold ar at hr; split at hr
        · next hc =>
          simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]
          exact (hpre.uo.2.1 hc).2.2.1
        · simp at hr
    · simp only [stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Nat.add_sub_cancel_left]; exact hpre.sti.1.2.2.1
      · simp only at hlt ⊢
        have hc : 0 < stCap s.mem st := by omega
        obtain ⟨-, -, hacc, -⟩ := hpre.sti.1.2.2.2.2.1 hc
        exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    · exact hws2 r hr hlt

/-- the drs window at its entry `RSP - 312`: exactly `[RSP - 41272, RSP - 216)` -/
theorem win_drs {X : State} {sp : Nat} (h : (X.regs 4).toNat = sp - 312) (h0 : 41272 ≤ sp) :
    win X 40960 96 = [(sp - 41272, sp - 216)] := by
  simp only [win, h]
  rw [Nat.sub_sub, show 312 + 40960 = 41272 from rfl, show sp - 312 + 96 = sp - 216 by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`DrsPre` at the call `q.divRecursiveStep(stk, u, v, 0)`** (pure): `X` = the state at its entry -/
theorem dr_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (X : State)
    (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 312) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hF : MemFrame S.mem X.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]))
    (hFL : LiveFrame S.mem X.mem Lq [(qp, qp + 8 * qc)])
    (hreg : X.mem.regions = s.mem.regions) (hz : natVal X.mem qp (il - vl + 1) = 0)
    (hinvX : R.inv bq Lq (s.regs 14).toNat (view R.rt Lq X.mem))
    (hvS : X.mem.readLE ((s.regs 4).toNat - 304) 8 = t) (hlS : X.mem.readLE ((s.regs 4).toNat - 296) 8 = vl)
    (hcS : X.mem.readLE ((s.regs 4).toNat - 288) 8 = vl) {dcv : Nat} (hcost : dcv ≤ bq) :
    DrsPre R bq Lq dcv qp (il - vl + 1) qc st P (il + 1) C t vl vl X := by
  -- NOTE: no unfolded disjunction stays in the top-level context (omega would case-split on all of them)
  have hl := hE.lay
  have hpre := hE.pre
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hMU := hS.mem
  have hM := hMU.mem
  have hU := hS.ua
  have hQ := hS.qa
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF.accessible, hM.fr.accessible]
  -- reads of held ranges outside the window and `q`
  have rdY : ∀ a n, Held R Lq a n → (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      (a + n ≤ qp ∨ qp + 8 * qc ≤ a) → X.mem.readLE a n = S.mem.readLE a n := by
    intro a n hh hw hq
    rcases hh with hi | ho
    · exact hFL.readLE a n hi (by simp only [outside_cons, outside_nil, and_true]; exact hq)
    · refine hF.readLE a n ?_
      rw [outside_append, outside_append]
      exact ⟨⟨ho, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
        by simp only [outside_cons, outside_nil, and_true]; exact hq⟩
  have hw1 := w1_facts hE
  have hc0 := hw1.1
  have hc1 := hE.c1len
  have hrnd : vl ≤ StackNat.rnd vl ∧ StackNat.rnd vl ≤ vl + 3 := by simp only [StackNat.rnd]; omega
  have hsth := hpre.sti.1.2.1
  have hsw := hl.sw
  have hW : stW X.mem st = w1 := by
    simp only [stW]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (Nat.le_refl _) (by omega)))) (by omega)
      (by have := hQ.ps; unfold Apart at this; omega)]; exact hM.hw
  have hLn : stLen X.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (by omega) (by omega)))) (by omega)
      (by have := hQ.ps; unfold Apart at this; omega)]; exact hM.hlen
  have hCp : stCap X.mem st = c1 := by
    simp only [stCap]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (by omega) (by omega)))) (by omega)
      (by have := hQ.ps; unfold Apart at this; omega)]; exact hM.hcap
  have hga0 := hpre.ce.2.2.2.2.2.1
  have hgrt := hpre.ce.2.2.2.2.2.2.1
  have hgrd : X.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hF.readLE _ _ (by
      have hqg := hQ.pg
      unfold Apart at hga0 hqg
      rw [outside_append, outside_append]
      exact ⟨⟨hgrt, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
        by simp only [outside_cons, outside_nil, and_true]; omega⟩)]
    exact hMU.grd
  have htw0 := hpre.ce.2.2.2.2.2.2.2.2.2.2.2
  have htrt : Outside (s.fsBase.toNat - 8) 8 R.rt := hpre.ce.2.2.2.2.2.2.2.2.2.2.1
  have htls : X.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hF.readLE _ _ (by
      have hqt := hQ.ptl
      unfold Apart at htw0 hqt
      rw [outside_append, outside_append]
      exact ⟨⟨htrt, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
        by simp only [outside_cons, outside_nil, and_true]; omega⟩)]
    exact hM.tls
  have hx3 := hS.ext3
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48
  have ht48 := hl.t48
  have hteq := hE.t_eq
  -- values
  have hvt : 2 ^ 63 ≤ X.mem.readLE (t + 8 * (vl - 1)) 8 := by
    rw [rdY _ _ (hx3.held (hl.theld.sub (by omega) (by omega))) (by have := hl.tw; omega)
      (by have := hQ.pt; unfold Apart at this; omega)]; exact hS.vtop
  have huv : natVal X.mem P (il + 1) = natVal s.mem ip il * 2 ^ sh := by
    rw [← hS.uval]; unfold natVal
    exact rdY _ _ (hU.pheld.sub (Nat.le_refl _) (by omega)) (by have := hU.pw; omega)
      (by have := hQ.pu; unfold Apart at this; omega)
  have hroom : 2 * natVal X.mem P (il + 1) < 2 ^ (64 * (vl + (il - vl + 1))) := by
    rw [huv, show vl + (il - vl + 1) = il + 1 by omega]
    refine DivLargeMath.scale_u _ _ _ ?_ hS.sh63
    unfold natVal
    have := Janus.Arm64.Memory.readLE_lt s.mem ip (8 * il)
    rw [show (256 : Nat) ^ (8 * il) = 2 ^ (64 * il) by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this
    exact this
  have hdl : Extracted.program.DataLoaded X.mem :=
    dl_at2 hE hM (ws2 := scrB s ++ [(qp, qp + 8 * qc)]) (by rw [← List.append_assoc]; exact hF) (fun r hr hlt => by
      obtain ⟨-, ⟨-, -, hw⟩, -⟩ := hpre.ce
      simp only [regSP] at hw
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · simp only [scrB, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
      · simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]
        rw [← hM.fr.accessible]; exact hQ.pacc) (by rw [hreg])
  have hsf : Apart st 24 (w1 + 8 * (stLen s.mem st + StackNat.rnd vl)) (8 * (c1 - (stLen s.mem st + StackNat.rnd vl))) := by
    rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · have := hpre.hf; unfold Apart at this ⊢; omega
    · rcases hsth with hi | ho
      · obtain ⟨r, hr, h1, h2⟩ := hi
        have := hap r hr; unfold Apart at this ⊢; omega
      · have := outside_of_inRanges ho hin; unfold Apart; omega
  have hgaw := ga_ws hE
  have hgq : Apart qp (8 * qc) RunIface.gA 32 := by
    rcases hQ.ror with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · exact hpre.ga.1 (by omega)
    · have := outside_of_inRanges hgaw.2.1 hin; unfold Apart; omega
  have hgp : Apart P (8 * C) RunIface.gA 32 := by
    rcases hU.ror with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · exact hpre.ga.2.1 (by omega)
    · have := outside_of_inRanges hgaw.2.1 hin; unfold Apart; omega
  have hwd := win_drs hspn hsp0
  have hwin : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      Outside a n (win X 40960 96) := fun a n h => by
    rw [hwd]; simp only [outside_cons, outside_nil, and_true]; omega
  have hsp4 : (X.regs 4).toNat + 8 = (s.regs 4).toNat - 304 ∧ (X.regs 4).toNat + 16 = (s.regs 4).toNat - 296 ∧
      (X.regs 4).toNat + 24 = (s.regs 4).toNat - 288 := by omega
  unfold DrsPre DrsPreW
  simp only [hW, hLn, hCp]
  refine ⟨?ce, hpre.sv, ?gl, by omega, hq40, by omega, hc40, Nat.le_refl _, by omega, hv2, ⟨by omega, by omega⟩, hvt,
    hz, hroom,
    ⟨?qacc, by omega, hQ.pheld.sub (Nat.le_refl _) (by omega), ?qw, ?qg⟩,
    ⟨?pacc, by omega, hU.pheld.sub (Nat.le_refl _) (by omega), ?pw, ?pg⟩,
    ⟨?tacc, ht48, hx3.held hl.theld, hwin _ _ hl.tw, ?tg, hx3.held hl.theld, ht48⟩, ?qp, ?qt, ?pt, ?stk, ?stlen,
    ⟨?sq, ?fq⟩, ⟨?sp, ?fp⟩, ⟨?st, ?ft⟩, hpre.wbap, hsf, ?stfw, ⟨?gq, ?gp, ?gs, ?gf⟩, hcost, by rw [h14]; exact hinvX,
    by rw [hsp4.1]; exact hvS, by rw [hsp4.2.1]; exact hlS, by rw [hsp4.2.2]; exact hcS,
    ⟨?tq, ?tp, ?ts, ?tf⟩⟩
  all_goals clear hroom
  case ce =>
    obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, -, hga, hgr, -, hro, ⟨⟨htb, htr, htg⟩, -, htw⟩⟩ := hpre.ce
    simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htb htr htg
    have hLq := lsep_of hE hx3
    unfold Apart at hga htw
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hdl, ?_, ?_, by rw [h14]; exact hgr, ?_, hro, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · simp only [regG]; rw [h14]; exact hg1
    · simp only [regG, stackguard0Offset]; rw [h14, hXacc]; exact hg2
    · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [h14, hgrd, hspn]; omega
    · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
    · simp only [regSP]; rw [hspn]; omega
    · simp only [regSP]; rw [hspn]; omega
    · simp only [regSP]; rw [hXacc, hspn, show (s.regs 4).toNat - 312 - 40960 = (s.regs 4).toNat - 41272 by omega]
      exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hspn]; omega
    · rw [hspn, show (s.regs 4).toNat - 312 - 40960 = (s.regs 4).toNat - 41272 by omega]
      exact hout.of_sub (by omega) (by omega)
    · rw [hspn, h14, show (s.regs 4).toNat - 312 - 40960 = (s.regs 4).toNat - 41272 by omega]; unfold Apart; omega
    · intro r hr; have := hLq r hr
      rw [hwd]; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [hfs]; exact htb
    · rw [hfs, hXacc]; exact htr
    · simp only [regG]; rw [hfs, h14]; exact htls
    · rw [hfs]; exact htrt
    · rw [hfs, hspn, show (s.regs 4).toNat - 312 - 40960 = (s.regs 4).toNat - 41272 by omega]; unfold Apart; omega
  case gl =>
    refine globals_frame' hpre.gl (ws := win s 41272 112 ++ wsL zp zc up uc vl t ++ stkWs s.mem st ++ scrB s ++
      [(qp, qp + 8 * qc)]) ((mfTrans hM.fr hF).mono fun a n ho => ?_) ?_ ?_
    · simp only [outside_append] at ho ⊢
      obtain ⟨h0, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ho
      exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, ⟨h0, h4⟩, h5⟩
    · rw [outside_append]
      refine ⟨hgaw.1, ?_⟩
      have := hgq; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    · intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h; exact hwin a n h
  case qacc => rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hQ.pacc (Nat.le_refl _) (by omega)
  case qw => exact hwin _ _ (by have := hQ.pw; omega)
  case qg => have := hQ.pg; rw [h14]; unfold Apart at this ⊢; omega
  case pacc => rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hU.pacc (Nat.le_refl _) (by omega)
  case pw => exact hwin _ _ (by have := hU.pw; omega)
  case pg => have := hU.pg; rw [h14]; unfold Apart at this ⊢; omega
  case tacc => rw [hXacc]; exact Janus.Arm64.Memory.accessible_read_of_write _ hE.scr.acc
  case qp => have := hQ.pu; unfold Apart at this ⊢; omega
  case qt => have := hQ.pt; unfold Apart at this ⊢; omega
  case pt => have := hU.pvt; unfold Apart at this ⊢; omega
  case stk =>
    obtain ⟨hw18, hw1acc, -, hw148⟩ := hE.w1live hc0
    have h1 := hw1.2.1; have h2 := hw1.2.2.1
    refine ⟨⟨hpre.sti.1.1, hx3.held (hE.ext.held hsth), by rw [hXacc]; exact hpre.sti.1.2.2.1, hpre.sti.1.2.2.2.1, ?_,
      ?_, ?_⟩, hwin _ _ hsw, by rw [h14]; exact hpre.sti.2.2.1, ?_⟩
    · rw [hW, hCp]; intro _; exact ⟨hw18, hx3.held hw1acc, by rw [hXacc]; exact (hE.w1live hc0).2.2.1, hw148⟩
    · rw [hLn, hCp]; exact hc1
    · rw [hCp]; exact hE.c1b
    · rw [hW, hCp, h14]; intro _; exact ⟨hwin _ _ h1, h2⟩
  case stlen => exact ⟨by have := hpre.stl; omega, hc0, by unfold Apart; omega, hpre.st0, hU.p8, hQ.p8⟩
  case sq => exact hQ.ps.mono (by omega) (Nat.le_refl _)
  case fq => exact hQ.pf.mono (by omega) (Nat.le_refl _)
  case sp => exact hU.ps.mono (by omega) (Nat.le_refl _)
  case fp => exact hU.pf.mono (by omega) (Nat.le_refl _)
  case st => have := hl.ts; unfold Apart; omega
  case ft => unfold Apart; omega
  case stfw => exact hwin _ _ (by have := hw1.2.1; omega)
  case tg =>
    have h := hgaw.1
    simp only [outside_append, wsL, outside_cons] at h
    have := h.1.1.2.1; unfold Apart; omega
  case gq => exact hgq.mono (by omega) (Nat.le_refl _)
  case gp => exact hgp.mono (by omega) (Nat.le_refl _)
  case gs => exact hpre.ga.2.2.1
  case gf => exact hgaw.2.2.symm
  case tq => have := hQ.ptl; rw [hfs]; unfold Apart at this ⊢; omega
  case tp => have := hU.pt; rw [hfs]; unfold Apart at this ⊢; omega
  case ts => rw [hfs]; exact hpre.stt
  case tf => rw [hfs]; exact hw1.2.2.2.2.2.2

end FvModexp.Amd64.DivLarge
