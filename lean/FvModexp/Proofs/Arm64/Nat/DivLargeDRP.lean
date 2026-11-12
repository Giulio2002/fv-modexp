import FvModexp.Proofs.Arm64.Nat.DivLargeDBP

/-!
# `divLarge` (arm64): the precondition of `q.divRecursiveStep(stk, u, v, 0)` at its call (pure)

`n ≥ divRecursiveThreshold`: `divRecursive` (inlined, natdiv.go:740) clears `q` (`memclr`) and calls
`divRecursiveStep(stk, u, v, 0)`. At the call state `Y` (`SP = entry SP - 304`): memory = `AtJ`'s with the `scrB`
slots written and `q` cleared. `DrsPre`'s value condition `2·U' < 2^(64(n + m + 1))` holds since `U' = U·2^sh`,
`sh ≤ 63`, `U < 2^(64·len uIn)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)
open FvModexp.Arm64.RunIface (Globals)

namespace FvModexp.Arm64.DivLarge

-- NOTE: `omega` hits `maxRecDepth` on goals with `sp - 304 - 40960` (nested subtraction of a large literal); the
-- window bounds are rewritten to `sp - 41264` / `sp - 208` first (`e1`/`e2` in `dr_pre`).
theorem wsub {x n sp : Nat} (h : x + n ≤ sp - 41264 ∨ sp + 112 ≤ x) (h0 : 41264 ≤ sp) :
    x + n ≤ sp - 41264 ∨ sp - 208 ≤ x := by omega

theorem win_e {y sp : Nat} (h : y = sp - 304) (h0 : 41264 ≤ sp) : y - 40960 = sp - 41264 ∧ y + 96 = sp - 208 :=
  ⟨by rw [h, Nat.sub_sub], by omega⟩

theorem asub {x sp : Nat} (h : Apart x 8 (sp - 41264) (41264 + 112)) (h0 : 41264 ≤ sp) :
    Apart x 8 (sp - 41264) (40960 + 96) := by unfold Apart at h ⊢; omega

/-- the threshold globals and the write-barrier flag survive a frame that keeps them
(adapted from fv-modexp divmc's `NatSqr.globals_frame`, Proofs/Arm64/Nat/SqrKPre.lean) -/
theorem globals_frame' {R : RtInv} {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : Globals R m w)
    (hF : MemFrame m m' (R.rt ++ ws)) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    Globals R m' w' := by
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
    Outside RunIface.gA 32 (winA s 41264 112 ++ wsL zp zc up uc vl t ++ stkWs s.mem st ++ scrB s) ∧
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
    · simp only [winA, outside_cons, outside_nil, and_true]; omega
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

set_option maxRecDepth 20000 in
theorem dl_at2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    (hM : Mem R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk M)
    {ws2 : List (Nat × Nat)} (hF : MemFrame M M' (R.rt ++ ws2))
    (hws2 : ∀ r ∈ ws2, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true) (hreg : M'.regions = s.mem.regions) :
    Extracted.program.DataLoaded M' := by
  have hpre := hE.pre
  have hl := hE.lay
  have hsp0 := hl.sp0
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, hd, hout, -, -, -, hro⟩ := hpre.ce
  refine dataLoaded_frame hd hreg hro ((mfTrans hM.fr hF).mono fun a n ho => ?_) (ws := winA s 41264 112 ++
    wsL zp zc up uc vl t ++ stkWs s.mem st ++ ws2) ?_
  · simp only [outside_append] at ho ⊢
    obtain ⟨h0, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := ho
    exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h0, h4⟩
  · intro r hr hlt
    rw [List.mem_append, List.mem_append, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
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
        exact Memory.accessible_mono _ hacc (by omega) (by omega)
    · exact hws2 r hr hlt

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`DrsPre` at the call `q.divRecursiveStep(stk, u, v, 0)`** (pure): `Y` = the state at its entry -/
theorem dr_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (Y : State)
    (hsp : Y.sp = s.sp - 304#64) (h28 : Y.regs 28 = s.regs 28)
    (hF : MemFrame S.mem Y.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]))
    (hFL : LiveFrame S.mem Y.mem Lq [(qp, qp + 8 * qc)])
    (hreg : Y.mem.regions = s.mem.regions) (hz : natVal Y.mem qp (il - vl + 1) = 0)
    (hinvY : R.inv bq Lq (s.regs 28).toNat (view R.rt Lq Y.mem)) {dcv : Nat} (hcost : dcv ≤ bq) :
    DrsPre R bq Lq dcv qp (il - vl + 1) qc st P (il + 1) C t vl vl Y := by
  -- NOTE: no unfolded disjunction stays in the top-level context (omega would case-split on all of them)
  have hl := hE.lay
  have hpre := hE.pre
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hspn : Y.sp.toNat = s.sp.toNat - 304 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hMU := hS.mem
  have hM := hMU.mem
  have hU := hS.ua
  have hQ := hS.qa
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  have hXacc : ∀ a n w, Y.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF.accessible, hM.fr.accessible]
  -- reads of held ranges outside `scrB` and `q`
  have rdY : ∀ a n, Held R Lq a n → (a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a) →
      (a + n ≤ qp ∨ qp + 8 * qc ≤ a) → Y.mem.readLE a n = S.mem.readLE a n := by
    intro a n hh hw hq
    rcases hh with hi | ho
    · exact hFL.readLE a n hi (by simp only [outside_cons, outside_nil, and_true]; exact hq)
    · refine hF.readLE a n ?_
      rw [outside_append, outside_append]
      exact ⟨⟨ho, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
        by simp only [outside_cons, outside_nil, and_true]; exact hq⟩
  have hc0 := (w1_facts hE).1
  have hc1 := hE.c1len
  have hrnd : vl ≤ StackNat.rnd vl ∧ StackNat.rnd vl ≤ vl + 3 := by simp only [StackNat.rnd]; omega
  have hsth := hpre.sti.1.2.1
  have hW : stW Y.mem st = w1 := by
    simp only [stW]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (Nat.le_refl _) (by omega)))) (by have := hl.sw; omega)
      (by have := hQ.ps; unfold Apart at this; omega)]; exact hM.hw
  have hLn : stLen Y.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (by omega) (by omega)))) (by have := hl.sw; omega)
      (by have := hQ.ps; unfold Apart at this; omega)]; exact hM.hlen
  have hCp : stCap Y.mem st = c1 := by
    simp only [stCap]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (by omega) (by omega)))) (by have := hl.sw; omega)
      (by have := hQ.ps; unfold Apart at this; omega)]; exact hM.hcap
  have hgrd : Y.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hF.readLE _ _ (by
      have := hpre.ce.2.2.2.2.1; have hqg := hQ.pg
      unfold Apart at this hqg
      rw [outside_append, outside_append]
      exact ⟨⟨hpre.ce.2.2.2.2.2.1, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
        by simp only [outside_cons, outside_nil, and_true]; omega⟩)]
    exact hMU.grd
  have hx3 := hS.ext3
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48
  have ht48 := hl.t48
  have hteq := hE.t_eq
  have hvo := hpre.vo
  -- values
  have hvt : 2 ^ 63 ≤ Y.mem.readLE (t + 8 * (vl - 1)) 8 := by
    rw [rdY _ _ (hx3.held (hl.theld.sub (by omega) (by omega))) (by have := hl.tw; omega)
      (by have := hQ.pt; unfold Apart at this; omega)]; exact hS.vtop
  have huv : natVal Y.mem P (il + 1) = natVal s.mem ip il * 2 ^ sh := by
    rw [← hS.uval]; unfold natVal
    exact rdY _ _ (hU.pheld.sub (Nat.le_refl _) (by omega)) (by have := hU.pw; omega)
      (by have := hQ.pu; unfold Apart at this; omega)
  have hroom : 2 * natVal Y.mem P (il + 1) < 2 ^ (64 * (vl + (il - vl + 1))) := by
    rw [huv, show vl + (il - vl + 1) = il + 1 by omega]
    refine DivLargeMath.scale_u _ _ _ ?_ hS.sh63
    unfold natVal
    have := Memory.readLE_lt s.mem ip (8 * il)
    rw [show (256 : Nat) ^ (8 * il) = 2 ^ (64 * il) by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this
    exact this
  have hdl : Extracted.program.DataLoaded Y.mem :=
    dl_at2 hE hM (ws2 := scrB s ++ [(qp, qp + 8 * qc)]) (by rw [← List.append_assoc]; exact hF) (fun r hr hlt => by
      obtain ⟨-, ⟨-, -, -, hw⟩, -⟩ := hpre.ce
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · simp only [scrB, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
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
  unfold DrsPre DrsPreW
  simp only [hW, hLn, hCp]
  refine ⟨?ce, hpre.sv, ?gl, by omega, hq40, by omega, hc40, Nat.le_refl _, hvo.1, hv2, ⟨by omega, by omega⟩, hvt, hz, hroom,
    ⟨?qacc, by omega, hQ.pheld.sub (Nat.le_refl _) (by omega), ?qw, ?qg⟩,
    ⟨?pacc, by omega, hU.pheld.sub (Nat.le_refl _) (by omega), ?pw, ?pg⟩,
    ⟨?tacc, ht48, hx3.held hl.theld, ?tw, ?tg, hx3.held hl.theld, ht48⟩, ?qp, ?qt, ?pt, ?stk, ?stlen,
    ⟨?sq, ?fq⟩, ⟨?sp, ?fp⟩, ⟨?st, ?ft⟩, hpre.wbap, hsf, ?stfw, ⟨?gq, ?gp, ?gs, ?gf⟩, hcost, by rw [h28]; exact hinvY⟩
  all_goals clear hroom
  case ce =>
    obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, hro⟩ := hpre.ce
    have hLq := lsep_of hE hx3
    refine ⟨⟨by rw [h28]; exact hg1, by rw [h28, hXacc]; exact hg2, by rw [h28, hgrd, hspn]; omega⟩,
      ⟨by rw [hspn]; omega, by rw [hspn]; omega, by rw [hspn]; omega, ?_⟩, hdl, ?_, ?_, by rw [h28]; exact hgr, ?_, hro⟩
    · rw [hXacc, hspn]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hspn]; exact hout.of_sub (by omega) (by omega)
    · rw [(win_e hspn hsp0).1, h28]; exact asub hga hsp0
    · intro r hr; have := hLq r hr
      simp only [win, outside_cons, outside_nil, and_true]; rw [(win_e hspn hsp0).1, (win_e hspn hsp0).2]; exact wsub this hsp0
  case gl =>
    refine globals_frame' hpre.gl (ws := winA s 41264 112 ++ wsL zp zc up uc vl t ++ stkWs s.mem st ++ scrB s ++
      [(qp, qp + 8 * qc)]) ((mfTrans hM.fr hF).mono fun a n ho => ?_) ?_ ?_
    · simp only [outside_append] at ho ⊢
      obtain ⟨h0, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ho
      exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, ⟨h0, h4⟩, h5⟩
    · rw [outside_append]
      refine ⟨hgaw.1, ?_⟩
      have := hgq; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    · intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [(win_e hspn hsp0).1, (win_e hspn hsp0).2]; exact wsub h hsp0
  case qacc => rw [hF.accessible]; exact Memory.accessible_mono _ hQ.pacc (Nat.le_refl _) (by omega)
  case qw => have := hQ.pw; simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  case qg => have := hQ.pg; rw [h28]; unfold Apart at this ⊢; omega
  case pacc => rw [hF.accessible]; exact Memory.accessible_mono _ hU.pacc (Nat.le_refl _) (by omega)
  case pw => have := hU.pw; simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  case pg => have := hU.pg; rw [h28]; unfold Apart at this ⊢; omega
  case tacc => rw [hXacc]; exact Memory.accessible_read_of_write _ hE.scr.acc
  case tw => have := hl.tw; simp only [win, outside_cons, outside_nil, and_true]; rw [(win_e hspn hsp0).1, (win_e hspn hsp0).2]; exact wsub this hsp0
  case qp => have := hQ.pu; unfold Apart at this ⊢; omega
  case qt => have := hQ.pt; unfold Apart at this ⊢; omega
  case pt => have := hU.pt; unfold Apart at this ⊢; omega
  case stk =>
    unfold EvenHyp.StkIn ExpHyp.StackOK' StkOK
    simp only [hW, hLn, hCp]
    obtain ⟨hw18, hw1h, hw1acc, hw148⟩ := hE.w1live hc0
    have h1 := (w1_facts hE).2.1; have h2 := (w1_facts hE).2.2.1
    refine ⟨⟨hpre.sti.1.1, hx3.held (hE.ext.held hsth), by rw [hXacc]; exact hpre.sti.1.2.2.1, hpre.sti.1.2.2.2.1,
      fun _ => ⟨hw18, hx3.held hw1h, by rw [hXacc]; exact hw1acc, hw148⟩, hc1, hE.c1b⟩, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
    · have := hl.sw; simp only [win, outside_cons, outside_nil, and_true]; rw [(win_e hspn hsp0).1, (win_e hspn hsp0).2]; exact wsub this hsp0
    · rw [h28]; exact hpre.sti.2.2.1
    · simp only [win, outside_cons, outside_nil, and_true]; rw [(win_e hspn hsp0).1, (win_e hspn hsp0).2]; exact wsub h1 hsp0
    · rw [h28]; exact h2
  case stlen => have := hpre.stl; omega
  case sq => exact hQ.ps.mono (by omega) (Nat.le_refl _)
  case fq => exact hQ.pf.mono (by omega) (Nat.le_refl _)
  case sp => exact hU.ps.mono (by omega) (Nat.le_refl _)
  case fp => exact hU.pf.mono (by omega) (Nat.le_refl _)
  case st => have := hl.ts; unfold Apart; omega
  case ft => unfold Apart; omega
  case stfw =>
    have h1 := (w1_facts hE).2.1
    simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  case tg =>
    have h := hgaw.1
    simp only [outside_append, wsL, outside_cons] at h
    have := h.1.1.2.1; unfold Apart; omega
  case gq => exact hgq.mono (by omega) (Nat.le_refl _)
  case gp => exact hgp.mono (by omega) (Nat.le_refl _)
  case gs => exact hpre.ga.2.2.1
  case gf => exact hgaw.2.2.symm

end FvModexp.Arm64.DivLarge
