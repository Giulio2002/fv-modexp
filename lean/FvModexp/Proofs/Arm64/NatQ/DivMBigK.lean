import FvModexp.Proofs.Arm64.Nat.DivMStk
import FvModexp.Proofs.Arm64.Nat.DivFree
import FvModexp.Proofs.Arm64.NatQ.DivMJoin

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivMBigK.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64), `stk == nil`: pure facts around the `divLarge` call and the deferred `stk.free()`

* `NewStk.frame`: the new stack survives frames outside `R.rt` (the defer record writes).
* `slots_keepM`: `divLarge` (window `[SP' - 41264, SP' + 112)` minus the saved FP/LR, `SP' = SP - 240`) keeps
  `nat.div`'s saved FP/LR (`[SP - 248, SP - 232)`) and everything at or above `SP - 128` (defer bits, the closure record).
* `freePreD`: `DivFree.Pre` at the closure's entry (`SP' = SP - 240`, `X26 = SP - 32`, stack word `SP - 24`).
* `dsumD`: `DivFree.sum` lifted to `LibDiv` (`Summary.of_codeIn`).
Adapted from agent expmc's `ExpN.freePre`/`dwSum` (Arm64/Exp/NNilKP.lean, NNilK.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open FvModexp.Arm64.DivNil

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem NewStk.frame {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {M M' : Memory} {st : Nat}
    {ws : List (Nat × Nat)} (hN : NewStk R L L1 b b1 g M st) (hF : MemFrame M M' ws)
    (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) : NewStk R L L1 b b1 g M' st := by
  obtain ⟨hL1, hrs, h0, h8, h48, hacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hbb, hbb', hinv⟩ := hN
  have hhd : InRanges st 24 R.rt := by
    have := (hrs (st, st + 24) (List.mem_cons_self ..)).1
    simpa only [Nat.add_sub_cancel_left] using this
  have ho := outside_of_rt hhd hws
  have ew : stW M' st = stW M st := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have el : stLen M' st = stLen M st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have ec : stCap M' st = stCap M st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have hrE : stkRs M' st = stkRs M st := stkRs_congr ew ec
  unfold NewStk
  rw [hrE, ew, el, ec]
  exact ⟨hL1, hrs, h0, h8, h48, by rw [hF.accessible]; exact hacc, hlen, hcap, hc0, hw8, hw48,
    fun hc => by rw [hF.accessible]; exact hwacc hc, hdis, hbb, hbb',
    RtInv.inv_frame' hF (fun r hr => Or.inl (hws r hr)) (by rw [hL1] at hinv ⊢; exact hinv)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `divLarge` keeps `nat.div`'s saved FP/LR and its slots at or above `SP - 128` -/
theorem slots_keepM {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {st u uc : Nat} {s X T : State}
    (hN : NewStk R L L1 b b1 g X.mem st) (hb' : 41504 ≤ s.sp.toNat)
    (hwout : Outside (s.sp.toNat - 41504) (41504 + 112) R.rt)
    (hu : 0 < uc → Outside u (8 * uc) (win s 41504 112)) (hsp : X.sp = s.sp - 240#64)
    (hmf : MemFrame X.mem T.mem (R.rt ++ winA X 41264 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    (a n : Nat) (ha : (s.sp.toNat - 248 ≤ a ∧ a + n ≤ s.sp.toNat - 232) ∨
      (s.sp.toNat - 128 ≤ a ∧ a + n ≤ s.sp.toNat + 112)) :
    T.mem.readLE a n = X.mem.readLE a n := by
  obtain ⟨x1, x2, x3, x4, -⟩ := spX hsp hb'
  have hrt : Outside a n R.rt := hwout.of_sub (by omega) (by omega)
  have hhd : InRanges st 24 R.rt := hN.hdr.1
  have h1 := out_inR2 hrt hhd
  have h2 : a + n ≤ stW X.mem st + 8 * stLen X.mem st ∨ stW X.mem st + 8 * stCap X.mem st ≤ a := by
    rcases Nat.eq_zero_or_pos (stCap X.mem st) with hc | hc
    · have e1 := hN.2.2.2.2.2.2.2.2.1 hc; have e2 := hN.2.2.2.2.2.2.1; rw [hc, e1, e2]; omega
    · have := out_inR2 hrt (hN.arr hc).1; omega
  have hu' : 0 < uc → a + n ≤ u ∨ u + 8 * uc ≤ a := fun hc => by
    have := hu hc; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  refine hmf.readLE a n ?_
  simp only [outside_append, stkWs, winA, outside_cons, outside_nil, and_true, x1, x2, x3, x4]
  exact ⟨⟨⟨hrt, by omega, by omega⟩, outside_ar (fun h => absurd h (by decide)), outside_ar hu'⟩, by omega, h2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `slots_keepM` at the six slots `nat.div`'s epilogue reads (saved LR/FP, defer bit, closure record) -/
theorem slots6 {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {st u uc : Nat} {s X T : State}
    (hN : NewStk R L L1 b b1 g X.mem st) (hb' : 41504 ≤ s.sp.toNat)
    (hwout : Outside (s.sp.toNat - 41504) (41504 + 112) R.rt)
    (hu : 0 < uc → Outside u (8 * uc) (win s 41504 112)) (hsp : X.sp = s.sp - 240#64)
    (hmf : MemFrame X.mem T.mem (R.rt ++ winA X 41264 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    {lr fp : Nat}
    (mlr : X.mem.readLE (s.sp.toNat - 240) 8 = lr) (mfp : X.mem.readLE (s.sp.toNat - 248) 8 = fp)
    (mfl : X.mem.readLE (s.sp.toNat - 122) 1 = 1) (mdw : X.mem.readLE (s.sp.toNat - 32) 8 = dwD)
    (mst : X.mem.readLE (s.sp.toNat - 24) 8 = st) (mrc : X.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32) :
    T.mem.readLE (s.sp.toNat - 240) 8 = lr ∧ T.mem.readLE (s.sp.toNat - 248) 8 = fp ∧
      T.mem.readLE (s.sp.toNat - 122) 1 = 1 ∧ T.mem.readLE (s.sp.toNat - 32) 8 = dwD ∧
      T.mem.readLE (s.sp.toNat - 24) 8 = st ∧ T.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32 := by
  have hk := slots_keepM hN hb' hwout hu hsp hmf
  exact ⟨(hk _ _ (Or.inl ⟨by omega, by omega⟩)).trans mlr, (hk _ _ (Or.inl ⟨by omega, by omega⟩)).trans mfp,
    (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans mfl, (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans mdw,
    (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans mst, (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans mrc⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the stack-guard word survives `divLarge` and the epilogue's slot writes -/
theorem guardS {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 : Nat} {st u uc : Nat} {s X : State} {mT m2 : Memory}
    (hN : NewStk R L L1 b b1 (s.regs 28).toNat X.mem st) (hb' : 41504 ≤ s.sp.toNat)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 41504) (41504 + 112))
    (hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hgu : 0 < uc → Apart u (8 * uc) ((s.regs 28).toNat + 16) 8) (hsp : X.sp = s.sp - 240#64)
    (hF : MemFrame s.mem X.mem (R.rt ++ winA s 41504 112))
    (hmf : MemFrame X.mem mT (R.rt ++ winA X 41264 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    (hF2 : MemFrame mT m2 [(s.sp.toNat - 80, s.sp.toNat - 32), (s.sp.toNat - 121, s.sp.toNat - 120)]) :
    m2.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
  unfold Apart at hga
  have hws := hN.outWs hgr
  obtain ⟨x1, x2, x3, x4, -⟩ := spX hsp hb'
  rw [hF2.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; omega), hmf.readLE _ 8 ?_, hF.readLE _ 8 ?_]
  · simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩
  · simp only [outside_append]
    refine ⟨⟨⟨hgr, ?_⟩, outside_ar (fun h => absurd h (by decide)), outside_ar fun hc => ?_⟩, hws⟩
    · simp only [winA, outside_cons, outside_nil, and_true, x1, x2, x3, x4]; omega
    · have := hgu hc; unfold Apart at this; omega

/-- `deferwrap1` (`DivFree.sum`, `StkSh` pool shape) as a callee of `LibDiv` -/
theorem dsumD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibDiv.program.link impl) dwD (DivFree.Pre R b L rs) (DivFree.Post R b L rs) := by
  have hsub : ∀ x, LibDivFree.names.contains x = true → LibDiv.names.contains x = true := by
    intro x hx
    have : x = DivFree.fn := by simpa [LibDivFree.names, DivFree.fn] using hx
    subst this; decide
  have hc := codeIn_restrict_mono hap hsub
  rw [← LibDivFree.eq_only, ← LibDiv.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn hc (DivFree.sum impl R hput b L rs)
  rwa [show segAddr Extracted.program DivFree.fn = dwD by decide] at h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closure's context at its entry `S` (`SP' = sp - 240`, `X26 = sp - 32`, `X30 = dwRD`) -/
theorem freePreD {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b' g sp st : Nat} {M1 : Memory} {S : State}
    (hN : NewStk R L L1 b b1 g M1 st)
    (hsp : S.sp.toNat = sp - 240) (h26 : (S.regs 26).toNat = sp - 32) (h30 : (S.regs 30).toNat = 1807612)
    (h28 : (S.regs 28).toNat = g)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible (g + 16) 8 false = true) (hg3 : S.mem.readLE (g + 16) 8 + 41504 < sp)
    (hgo1 : Apart (g + 16) 8 (sp - 41504) (41504 + 112)) (hgo2 : Outside (g + 16) 8 R.rt)
    (hal : sp % 16 = 0) (hKs : 41504 ≤ sp) (hsp2 : sp + 112 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp - 41504) (41504 + 112) true = true)
    (hwout : Outside (sp - 41504) (41504 + 112) R.rt) (hLs : LiveSep L [(sp - 41504, sp + 112)])
    (h24 : S.mem.readLE (sp - 24) 8 = st) (hok : StkOK S.mem R L2 st) (hlen : stLen S.mem st = 0)
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0)
    (hdis : 0 < stCap S.mem st → Apart st 24 (stW S.mem st) (8 * stCap S.mem st))
    (hrs : ∀ x ∈ stkRs S.mem st, x ∈ L2) (hx : LiveExt R L1 L2)
    (hput : R.ok (cA "sync.(*Pool).Put") [Free.poolA]) (hinv : R.inv b' L2 g (view R.rt L2 S.mem)) :
    DivFree.Pre R b' L2 (stkRs S.mem st) S := by
  have hst0 : 0 < st := hN.2.2.1
  have hso : Free.stkOf S = st := by
    show S.mem.readLE ((S.regs 26).toNat + 8) 8 = st
    rw [h26, show sp - 32 + 8 = sp - 24 by omega]; exact h24
  have hhd := hN.hdr.1
  have hsh := StkSh.of_ok hok hst0 hlen hc0 hdis
  have hhg := out_inR2 hgo2 hhd
  have hhw := out_inR2 hwout hhd
  unfold Apart at hgo1
  have hGd : GuardOK S 4144 := by
    unfold GuardOK; rw [h28, hsp]; exact ⟨hg1, hg2, by omega⟩
  have hSo : StackOK S 4144 0 := by
    unfold StackOK; rw [hsp]
    exact ⟨by omega, by omega, by omega, Memory.accessible_mono _ hacc (by omega) (by omega)⟩
  unfold DivFree.Pre
  rw [hso, h28, hsp, h26, h30]
  refine ⟨hGd, hSo, by decide, by decide, by omega,
    Memory.accessible_mono _ (Memory.accessible_read_of_write _ hacc) (by omega) (by omega),
    by unfold Apart; omega, hsh.1, hsh.2.2, by unfold Apart; omega, by unfold Apart; omega,
    by unfold Apart; omega, hgo2, hrs, hput, hinv, ?_, hwout.of_sub (by omega) (by omega)⟩
  refine LiveSep.sub_win (lo := sp - 41504) (hi := sp + 112) ?_ (by omega) (by omega)
  refine liveSep_ext hx (hN.liveSep hLs fun q hq => ?_) fun q hq => ?_
  all_goals
    simp only [List.mem_singleton] at hq; subst hq; simp only
    rwa [show sp + 112 - (sp - 41504) = 41504 + 112 by omega]

end FvModexp.Arm64.Q.NatDiv
