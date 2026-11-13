import FvModexp.Proofs.Amd64.Nat.DivMStk
import FvModexp.Proofs.Amd64.Nat.DivFreeS
import FvModexp.Proofs.Amd64.NatQ.DivMEpi

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`: pure facts around the `divLarge` call and the deferred `stk.free()` (top s42)

Twin of Arm64/NatQ/DivMBigK.lean (`sp` = the entry `RSP`; `divLarge`'s entry `RSP = sp - 240`, window
`win X 41272 112` = `[sp - 41512, sp - 128)`).
* `NewStk.frame`: the new stack survives frames outside `R.rt`.
* `slots_keepM`: `divLarge` keeps everything of `nat.div`'s frame at or above `sp - 128` (defer bits, the closure record,
  the saved `RBP`, the return address).
* `slots6`: `slots_keepM` at the six slots the epilogue reads.
* `guardS`: the stack-guard word survives `divLarge` and the epilogue's writes.
* `dsumM`: `Free.sumDS` (`StkSh` pool shape) lifted to `LibDiv`.
* `freePreM`: `Free.PreS` at the closure's entry (`RSP = sp - 240`, `RDX = sp - 32`, stack word at `sp - 24`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem NewStk.frame {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {M M' : Janus.Arm64.Memory} {st : Nat}
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
/-- `divLarge` keeps `nat.div`'s slots at or above `sp - 128` -/
theorem slots_keepM {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {st u uc : Nat} {s X T : State}
    (hN : NewStk R L L1 b b1 g X.mem st) (hb' : 41512 ≤ (s.regs 4).toNat)
    (hwout : Outside ((s.regs 4).toNat - 41512) (41512 + 112) R.rt)
    (hu : 0 < uc → Outside u (8 * uc) (win s 41512 112)) (hsp : X.regs 4 = s.regs 4 - 240#64)
    (hmf : MemFrame X.mem T.mem (R.rt ++ win X 41272 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    (a n : Nat) (ha : (s.regs 4).toNat - 128 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 112) :
    T.mem.readLE a n = X.mem.readLE a n := by
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
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
  simp only [outside_append, stkWs, win, outside_cons, outside_nil, and_true, hspn]
  exact ⟨⟨⟨hrt, by omega⟩, outside_ar (fun h => absurd h (by decide)), outside_ar hu'⟩, by omega, h2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `slots_keepM` at the six slots the epilogue reads (return address, saved `RBP`, defer bit, closure record) -/
theorem slots6 {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {st u uc : Nat} {s X T : State}
    (hN : NewStk R L L1 b b1 g X.mem st) (hb' : 41512 ≤ (s.regs 4).toNat)
    (hwout : Outside ((s.regs 4).toNat - 41512) (41512 + 112) R.rt)
    (hu : 0 < uc → Outside u (8 * uc) (win s 41512 112)) (hsp : X.regs 4 = s.regs 4 - 240#64)
    (hmf : MemFrame X.mem T.mem (R.rt ++ win X 41272 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    {ra fp : Nat}
    (mra : X.mem.readLE (s.regs 4).toNat 8 = ra) (mfp : X.mem.readLE ((s.regs 4).toNat - 8) 8 = fp)
    (mfl : X.mem.readLE ((s.regs 4).toNat - 122) 1 = 1) (mdw : X.mem.readLE ((s.regs 4).toNat - 32) 8 = dwM)
    (mst : X.mem.readLE ((s.regs 4).toNat - 24) 8 = st)
    (mrc : X.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32) :
    T.mem.readLE (s.regs 4).toNat 8 = ra ∧ T.mem.readLE ((s.regs 4).toNat - 8) 8 = fp ∧
      T.mem.readLE ((s.regs 4).toNat - 122) 1 = 1 ∧ T.mem.readLE ((s.regs 4).toNat - 32) 8 = dwM ∧
      T.mem.readLE ((s.regs 4).toNat - 24) 8 = st ∧
      T.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32 := by
  have hk := slots_keepM hN hb' hwout hu hsp hmf
  exact ⟨(hk _ _ ⟨by omega, by omega⟩).trans mra, (hk _ _ ⟨by omega, by omega⟩).trans mfp,
    (hk _ _ ⟨by omega, by omega⟩).trans mfl, (hk _ _ ⟨by omega, by omega⟩).trans mdw,
    (hk _ _ ⟨by omega, by omega⟩).trans mst, (hk _ _ ⟨by omega, by omega⟩).trans mrc⟩

set_option maxRecDepth 100000 in
/-- outside `nat.div`'s window ⇒ outside `divLarge`'s (`RSP - 240`, `41272 + 112`) -/
theorem win240 {t a k : Nat} (hb : 41512 ≤ t)
    (h : a + k ≤ t - 41512 ∨ t + 112 ≤ a) :
    a + k ≤ t - 240 - 41272 ∨ t - 240 + 112 ≤ a := by omega

set_option maxRecDepth 100000 in
theorem gwin_aux {t g : Nat} (hb : 41512 ≤ t)
    (h : g + 16 + 8 ≤ t - 41512 ∨ t - 41512 + (41512 + 112) ≤ g + 16) :
    g + 16 + 8 ≤ t - 240 - 41272 ∨ t - 240 + 112 ≤ g + 16 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the stack-guard word survives `divLarge` and the epilogue's slot writes -/
theorem guardS {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 : Nat} {st u uc : Nat} {s X : State}
    {mT m2 : Janus.Arm64.Memory}
    (hN : NewStk R L L1 b b1 (s.regs 14).toNat X.mem st) (hb' : 41512 ≤ (s.regs 4).toNat)
    (hga : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 41512) (41512 + 112))
    (hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt)
    (hgu : 0 < uc → Apart u (8 * uc) ((s.regs 14).toNat + 16) 8) (hsp : X.regs 4 = s.regs 4 - 240#64)
    (hF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112))
    (hmf : MemFrame X.mem mT (R.rt ++ win X 41272 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    (hF2 : MemFrame mT m2 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120)]) :
    m2.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
  unfold Apart at hga
  have hws := hN.outWs hgr
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have o1 : Outside ((s.regs 14).toNat + 16) 8 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have ow : Outside ((s.regs 14).toNat + 16) 8 (win X 41272 112) := by
    simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; exact gwin_aux hb' hga
  have o2 : Outside ((s.regs 14).toNat + 16) 8
      (R.rt ++ win X 41272 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st) := by
    simp only [outside_append]
    exact ⟨⟨⟨hgr, ow⟩, outside_ar (fun h => absurd h (by decide)), outside_ar fun hc => by
      have := hgu hc; unfold Apart at this; omega⟩, hws⟩
  have o3 : Outside ((s.regs 14).toNat + 16) 8 (R.rt ++ win s 41512 112) := by
    simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩
  exact (hF2.readLE _ 8 o1).trans ((hmf.readLE _ 8 o2).trans (hF.readLE _ 8 o3))

set_option maxRecDepth 20000 in
/-- `deferwrap1` (`Free.sumDS`, `StkSh` pool shape) as a callee of `LibDiv` -/
theorem dsumM (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibDiv.program.link impl) dwM (Free.PreS R b L rs) (Free.Post R b L rs) := by
  have hc : CodeIn64 (LibDivFree.program.link impl) (LibDiv.program.link impl) := by
    rw [LibDivFree.eq_only, LibDiv.eq_only]
    exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide))
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc (Free.sumDS impl R hput b L rs)
  rwa [show segAddr Extracted.program Free.fnD = dwM by decide] at h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closure's context at its entry `S` (`RSP = sp - 240`, `RDX = sp - 32`, return address `dwRM`) -/
theorem freePreM {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b' g sp st : Nat} {M1 : Janus.Arm64.Memory}
    {S : State} (hN : NewStk R L L1 b b1 g M1 st)
    (hsp : (S.regs 4).toNat = sp - 240) (h2 : (S.regs 2).toNat = sp - 32)
    (hra : S.mem.readLE (sp - 240) 8 = dwRM) (h14 : (S.regs 14).toNat = g)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible (g + 16) 8 false = true)
    (hg3 : S.mem.readLE (g + 16) 8 + 41512 < sp)
    (hgo1 : Apart (g + 16) 8 (sp - 41512) (41512 + 112)) (hgo2 : Outside (g + 16) 8 R.rt)
    (hal : sp % 8 = 0) (hKs : 41512 ≤ sp) (hsp2 : sp + 112 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp - 41512) (41512 + 112) true = true)
    (hwout : Outside (sp - 41512) (41512 + 112) R.rt) (hLs : LiveSep L [(sp - 41512, sp + 112)])
    (h24 : S.mem.readLE (sp - 24) 8 = st) (hok : StkOK S.mem R L2 st) (hlen : stLen S.mem st = 0)
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0)
    (hdis : 0 < stCap S.mem st → Apart st 24 (stW S.mem st) (8 * stCap S.mem st))
    (hrs : ∀ x ∈ stkRs S.mem st, x ∈ L2) (hx : LiveExt R L1 L2)
    (hput : R.ok (cA "sync.(*Pool).Put") [Free.poolA]) (hinv : R.inv b' L2 g (view R.rt L2 S.mem)) :
    Free.PreS R b' L2 (stkRs S.mem st) S := by
  have hst0 : 0 < st := hN.2.2.1
  have hso : Free.stkOf S = st := by
    show S.mem.readLE ((S.regs 2).toNat + 8) 8 = st
    rw [h2, show sp - 32 + 8 = sp - 24 by omega]; exact h24
  have hhd := hN.hdr.1
  have hsh := StkSh.of_ok hok hst0 hlen hc0 hdis
  have hhg := out_inR2 hgo2 hhd
  have hhw := out_inR2 hwout hhd
  unfold Apart at hgo1
  unfold Free.PreS Free.Pre
  rw [hso, h14, hsp, h2]
  refine ⟨⟨hg1, hg2, by omega, by omega, by omega,
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega), by rw [hra]; decide, by omega,
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hacc) (by omega) (by omega),
    by unfold Apart; omega, hsh.1, by unfold Apart; omega, by unfold Apart; omega,
    by unfold Apart; omega, hgo2, hrs, hput, hinv, ?_, hwout.of_sub (by omega) (by omega)⟩, hsh.2.2⟩
  refine LiveSep.sub_win (lo := sp - 41512) (hi := sp + 112) ?_ (by omega) (by omega)
  refine liveSep_ext hx (hN.liveSep hLs fun q hq => ?_) fun q hq => ?_
  all_goals
    simp only [List.mem_singleton] at hq; subst hq; simp only
    rwa [show sp + 112 - (sp - 41512) = 41512 + 112 by omega]

end FvModexp.Amd64.Q.NatDiv
