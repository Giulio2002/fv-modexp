import FvModexp.Proofs.Amd64.Nat.DivLargeQRel
import FvModexp.Proofs.Amd64.Nat.DivLargeCallees

set_option autoImplicit false

/-!
# `divLarge` (amd64): the precondition of `q.divBasic(stk, u, v)` at its call (pure)

At the callee entry `X` (`RSP = entry RSP - 312`, return address pushed): memory = `AtJ`'s with the `q` slots
(`RSP - 64 … RSP - 40`), the stack args `v = (t, vl, vl)` (`RSP - 304 … RSP - 280`) and the return address written.
`q = (qp, m + 1)`, `u = (P, il + 1, C)`, `v = (t, vl)`; the room condition `U' < V'·2^(64(m+1))` holds since
`U < 2^(64 il)`, `V ≥ 2^(64(vl-1))`. Port of `Arm64/Nat/DivLargeDBP.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

namespace FvModexp.Amd64.DivLarge

/-- the room condition of `divBasic` (pure arithmetic) -/
theorem room_lt (U V c vl m : Nat) (hU : U < 2 ^ (64 * (vl + m))) (hV : 2 ^ (64 * (vl - 1)) ≤ V) (hv : 1 ≤ vl)
    (hc : 0 < c) : U * c < V * c * 2 ^ (64 * (m + 1)) := by
  have h1 : 2 ^ (64 * (vl + m)) = 2 ^ (64 * (vl - 1)) * 2 ^ (64 * (m + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2 : U < V * 2 ^ (64 * (m + 1)) :=
    Nat.lt_of_lt_of_le hU (by rw [h1]; exact Nat.mul_le_mul_right _ hV)
  rw [Nat.mul_assoc V c, Nat.mul_comm c, ← Nat.mul_assoc]
  exact Nat.mul_lt_mul_of_pos_right h2 hc

/-- a normalised nat of `n ≥ 1` words is at least `2^(64(n-1))` -/
theorem natVal_ge (m : Memory) (p n : Nat) (hn : 1 ≤ n) (ht : m.readLE (p + 8 * (n - 1)) 8 ≠ 0) :
    2 ^ (64 * (n - 1)) ≤ natVal m p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht ⊢
  rw [natVal_succ]
  have : 1 ≤ m.readLE (p + 8 * k) 8 := Nat.pos_of_ne_zero ht
  calc 2 ^ (64 * k) = 2 ^ (64 * k) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (64 * k) * m.readLE (p + 8 * k) 8 := Nat.mul_le_mul_left _ this
    _ ≤ _ := Nat.le_add_left _ _

/-- the call-preparation writes between `joinQ` and a division callee's entry: the stack args + return address and
the `q` slots -/
@[reducible] def callWs (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 312, (s.regs 4).toNat - 280), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 40)]

/-- `DataLoaded` at a state whose memory is `AtJ`'s with the call-preparation writes (pure) -/
theorem dl_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    (hM : Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk M)
    (hF : MemFrame M M' (callWs s)) (hreg : M'.regions = s.mem.regions) :
    Extracted.program.DataLoaded M' := by
  have hpre := hE.pre
  have hl := hE.lay
  have hsp0 := hl.sp0
  have hd : Extracted.program.DataLoaded s.mem := hpre.ce.2.2.2.1
  have hro : RoOut R := hpre.ce.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  refine dataLoaded_frame64 hd hreg hro ((mfTrans hM.fr hF).mono fun a n ho => ?_) (ws := win s 41272 112 ++
    wsL zp zc up uc vl t ++ stkWs s.mem st ++ callWs s) ?_
  · simp only [outside_append] at ho ⊢
    obtain ⟨h0, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := ho
    exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
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
    · simp only [callWs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega)
        (by simp only; omega)

/-- the stack array `(w1, c1)` after `stk.nat(n)`: non-empty, outside the window, apart from the guard word and the TLS
word, held -/
theorem w1_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) :
    0 < c1 ∧ (w1 + 8 * c1 ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ w1) ∧
      Apart w1 (8 * c1) ((s.regs 14).toNat + 16) 8 ∧ w1 % 8 = 0 ∧ Held R L1 w1 (8 * c1) ∧ w1 + 8 * c1 ≤ 2 ^ 48 ∧
      Apart (w1 + 8 * (stLen s.mem st + StackNat.rnd vl)) (8 * (c1 - (stLen s.mem st + StackNat.rnd vl)))
        (s.fsBase.toNat - 8) 8 := by
  have hpre := hE.pre
  have hv2 := hpre.v2
  have hc1 := hE.c1len
  have hc0 : 0 < c1 := by simp only [StackNat.rnd] at hc1; omega
  obtain ⟨a1, a2, -, a4⟩ := hE.w1live hc0
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  have hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt := hpre.ce.2.2.2.2.2.2.1
  have htr : Outside (s.fsBase.toNat - 8) 8 R.rt := hpre.ce.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hc0, ?_, ?_, a1, a2, a4, ?_⟩
  · rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · have := (hpre.sti.2.2.2 hc0).1
      simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := outside_of_inRanges hout hin; omega
  · rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · exact (hpre.sti.2.2.2 hc0).2
    · have := outside_of_inRanges hgr hin; unfold Apart; omega
  · rcases hE.arr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · have := hpre.stft; have hlc := hpre.sti.1.2.2.2.2.2.1
      rw [e1, e2]; unfold Apart at this ⊢; omega
    · have := outside_of_inRanges htr hin; unfold Apart; omega

/-- the budget of the division call (pure) -/
theorem bud_div {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {dc : Nat → Nat → Nat → Nat}
    {zp zc st up uc ip il vp vl : Nat} {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {bq : Nat}
    (h3 : b1 - makeCost (il + 1) - makeCost (il - vl + 1) ≤ bq) :
    max (stackNatCost (stLen s.mem st + StackNat.rnd vl) (vl + 1))
      (dc (stLen s.mem st + StackNat.rnd vl) (il + 1) vl) ≤ bq := by
  have h1 := hE.pre.cost
  have h2 := hE.bud
  simp only [cost] at h1
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`DivBasic.Pre` at the call `q.divBasic(stk, u, v)`** (pure): `X` = the state at `divBasic`'s entry -/
theorem db_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (X : State)
    (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 312) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hF : MemFrame S.mem X.mem (callWs s)) (hreg : X.mem.regions = s.mem.regions)
    (hvS : X.mem.readLE ((s.regs 4).toNat - 304) 8 = t) (hlS : X.mem.readLE ((s.regs 4).toNat - 296) 8 = vl)
    (hcost : stackNatCost (stLen s.mem st + StackNat.rnd vl) (vl + 1) ≤ bq) :
    DivBasic.Pre R bq Lq qp (il - vl + 1) st P (il + 1) C t vl X := by
  -- NOTE: no unfolded disjunction stays in the top-level context (omega would case-split on all of them)
  have hl := hE.lay
  have hpre := hE.pre
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hMU := hS.mem
  have hM := hMU.mem
  have hU := hS.ua
  have hQ := hS.qa
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF.accessible, hM.fr.accessible]
  have rdX : ∀ a n, (a + n ≤ (s.regs 4).toNat - 312 ∨ (s.regs 4).toNat - 280 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 40 ≤ a) → X.mem.readLE a n = S.mem.readLE a n :=
    fun a n h1 h2 => hF.readLE a n (by simp only [callWs, outside_cons, outside_nil, and_true]; exact ⟨h1, h2⟩)
  have hw1 := w1_facts hE
  have hc0 := hw1.1
  have hc1 := hE.c1len
  have hrnd : vl ≤ StackNat.rnd vl ∧ StackNat.rnd vl ≤ vl + 3 := by simp only [StackNat.rnd]; omega
  have hsw := hl.sw
  have hW : stW X.mem st = w1 := by
    simp only [stW]; rw [rdX _ _ (by omega) (by omega)]; exact hM.hw
  have hLn : stLen X.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]; rw [rdX _ _ (by omega) (by omega)]; exact hM.hlen
  have hCp : stCap X.mem st = c1 := by
    simp only [stCap]; rw [rdX _ _ (by omega) (by omega)]; exact hM.hcap
  have hga0 := hpre.ce.2.2.2.2.2.1
  have hgrd : X.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    unfold Apart at hga0
    rw [rdX _ _ (by omega) (by omega)]; exact hMU.grd
  have htw0 := hpre.ce.2.2.2.2.2.2.2.2.2.2.2
  have htls : X.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    unfold Apart at htw0
    rw [rdX _ _ (by omega) (by omega)]; exact hM.tls
  have hx3 := hS.ext3
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48
  have ht48 := hl.t48
  have hteq := hE.t_eq
  -- values
  have hvv : natVal X.mem t vl = natVal s.mem vp vl * 2 ^ sh := by
    rw [← hS.vval]; unfold natVal; exact rdX _ _ (by have := hl.tw; omega) (by have := hl.tw; omega)
  have huv : natVal X.mem P (il + 1) = natVal s.mem ip il * 2 ^ sh := by
    rw [← hS.uval]; unfold natVal; exact rdX _ _ (by have := hU.pw; omega) (by have := hU.pw; omega)
  have hvt : 2 ^ 63 ≤ X.mem.readLE (t + 8 * (vl - 1)) 8 := by
    rw [rdX _ _ (by have := hl.tw; omega) (by have := hl.tw; omega)]; exact hS.vtop
  have hroom : natVal X.mem P (il + 1) < natVal X.mem t vl * 2 ^ (64 * (il - vl + 1)) := by
    rw [huv, hvv]
    have hU' : natVal s.mem ip il < 2 ^ (64 * (vl + (il - vl))) := by
      rw [show vl + (il - vl) = il by omega]; unfold natVal
      have := Janus.Arm64.Memory.readLE_lt s.mem ip (8 * il)
      rw [show (256 : Nat) ^ (8 * il) = 2 ^ (64 * il) by
        rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this
      exact this
    have hV' : 2 ^ (64 * (vl - 1)) ≤ natVal s.mem vp vl := by
      refine natVal_ge s.mem vp vl (by omega) ?_
      rcases hpre.vn with h | h
      · omega
      · exact h
    exact room_lt _ _ _ vl (il - vl) hU' hV' (by omega) (Nat.two_pow_pos _)
  -- the live set
  have hinv : R.inv bq Lq (s.regs 14).toNat (view R.rt Lq X.mem) :=
    RtInv.inv_frame' hF (fun r hr => by
      simp only [callWs, List.mem_cons, List.not_mem_nil, or_false] at hr
      left
      rcases hr with rfl | rfl <;> exact hpre.ce.2.2.2.2.1.of_sub (by simp only; omega) (by simp only; omega)) hM.inv
  have hdl : Extracted.program.DataLoaded X.mem := dl_at hE hM hF hreg
  have hsth := hpre.sti.1.2.1
  -- the free part at `X` is inside `(w1, c1)`; the stack header is apart from it
  have hsf : Apart st 24 (w1 + 8 * (stLen s.mem st + StackNat.rnd vl)) (8 * (c1 - (stLen s.mem st + StackNat.rnd vl))) := by
    rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · have := hpre.hf; unfold Apart at this ⊢; omega
    · rcases hsth with hi | ho
      · obtain ⟨r, hr, h1, h2⟩ := hi
        have := hap r hr; unfold Apart at this ⊢; omega
      · have := outside_of_inRanges ho hin; unfold Apart; omega
  have hwin : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      Outside a n (win X 4424 88) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold DivBasic.Pre
  refine ⟨?ce, hpre.sv, ?wb, hpre.wbap, hv2, hvt, ?tacc, ht48, hx3.held hl.theld, hwin _ _ hl.tw,
    by omega, hcap, hc40, ?pacc, by omega, hU.pheld.sub (Nat.le_refl _) (by omega), ?pw, ?pg,
    by omega, ?qacc, by omega, hQ.pheld.sub (Nat.le_refl _) (by omega), ?qw, ?qg, ?qp, ?qt, ?pt,
    fun _ => Or.inr ⟨by omega, hroom⟩, ?stok, hwin _ _ hsw, ?stg, ?starr, ?stfg, ?stlen, ?sq, ?sp, ?stt, ?free,
    ?stfree, ?stfw, by rw [hLn]; exact hcost, by rw [h14]; exact hinv, by rw [hspn, show (s.regs 4).toNat - 312 + 8 = (s.regs 4).toNat - 304 by omega]; exact hvS,
    by rw [hspn, show (s.regs 4).toNat - 312 + 16 = (s.regs 4).toNat - 296 by omega]; exact hlS, ?qtl, ?ptl, by rw [hfs]; exact hpre.stt, ?stft⟩
  case wb => rw [hXacc]; exact hpre.gl.2.2.2.2.2.2.2.2.2.2.1
  case ce =>
    obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, hro, ⟨⟨htb, htr, htg⟩, htrt, htw⟩⟩ := hpre.ce
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
    · simp only [regSP]; rw [hXacc, hspn]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hspn]; omega
    · rw [hspn]; exact hout.of_sub (by omega) (by omega)
    · rw [hspn, h14]; unfold Apart; omega
    · intro r hr; have := hLq r hr
      simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · rw [hfs]; exact htb
    · rw [hfs, hXacc]; exact htr
    · simp only [regG]; rw [hfs, h14]; exact htls
    · rw [hfs]; exact htrt
    · rw [hfs, hspn]; unfold Apart; omega
  case tacc => rw [hXacc]; exact Janus.Arm64.Memory.accessible_read_of_write _ hE.scr.acc
  case pacc => rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hU.pacc (Nat.le_refl _) (by omega)
  case pw => exact hwin _ _ (by have := hU.pw; omega)
  case pg => have := hU.pg; rw [h14]; unfold Apart at this ⊢; omega
  case qacc => rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hQ.pacc (Nat.le_refl _) (by omega)
  case qw => exact hwin _ _ (by have := hQ.pw; omega)
  case qg => have := hQ.pg; rw [h14]; unfold Apart at this ⊢; omega
  case qp => have := hQ.pu; unfold Apart at this ⊢; omega
  case qt => have := hQ.pt; unfold Apart at this ⊢; omega
  case pt => have := hU.pvt; unfold Apart at this ⊢; omega
  case qtl => have := hQ.ptl; rw [hfs]; unfold Apart at this ⊢; omega
  case ptl => have := hU.pt; rw [hfs]; unfold Apart at this ⊢; omega
  case stok =>
    obtain ⟨hw18, hw1acc, -, hw148⟩ := hE.w1live hc0
    refine ⟨hpre.sti.1.1, hx3.held (hE.ext.held hsth), by rw [hXacc]; exact hpre.sti.1.2.2.1, hpre.sti.1.2.2.2.1, ?_, ?_, ?_⟩
    · rw [hW, hCp]; intro _; exact ⟨hw18, hx3.held hw1acc, by rw [hXacc]; exact (hE.w1live hc0).2.2.1, hw148⟩
    · rw [hLn, hCp]; exact hc1
    · rw [hCp]; exact hE.c1b
  case stg => rw [h14]; exact hpre.sti.2.2.1
  case starr =>
    have h1 := hw1.2.1; have h2 := hw1.2.2.1
    rw [hW, hCp, h14]; intro _
    exact ⟨hwin _ _ h1, h2⟩
  case stfg =>
    have h2 := hw1.2.2.1
    simp only [DivBasic.freeP, DivBasic.freeN, hW, hLn, hCp]; rw [h14]; unfold Apart at h2 ⊢; omega
  case stlen => rw [hLn]; have := hpre.stl; omega
  case sq => exact (hQ.ps.symm).mono (Nat.le_refl _) (by omega)
  case sp => exact (hU.ps.symm).mono (Nat.le_refl _) (by omega)
  case stt => have := hl.ts; unfold Apart; omega
  case free =>
    simp only [DivBasic.freeP, DivBasic.freeN, hW, hLn, hCp]
    refine ⟨(hQ.pf).mono (by omega) (Nat.le_refl _), (hU.pf).mono (by omega) (Nat.le_refl _), ?_⟩
    unfold Apart; omega
  case stfree =>
    simp only [DivBasic.freeP, DivBasic.freeN, hW, hLn, hCp]; exact hsf
  case stfw =>
    have h1 := hw1.2.1
    simp only [DivBasic.freeP, DivBasic.freeN, hW, hLn, hCp]
    exact hwin _ _ (by omega)
  case stft =>
    have h3 := hw1.2.2.2.2.2.2
    simp only [DivBasic.freeP, DivBasic.freeN, hW, hLn, hCp]; rw [hfs]; exact h3

end FvModexp.Amd64.DivLarge
