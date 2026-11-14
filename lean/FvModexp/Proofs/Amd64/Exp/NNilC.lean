import FvModexp.Proofs.Amd64.Exp.NNilK
import FvModexp.Proofs.Amd64.Exp.NRemP
import FvModexp.Proofs.Amd64.Exp.NMidME

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the downstream chain at the virtual entry (agent expmc s75; twin of
`Arm64.ExpN` NNilC)

After `Get`/`newobject` and the defer record (memory `M1`, new stack `st`, `NewStk`), the code joins the stack-given path
at the `rem` entry (`y == 1`) or at `J4`. `contR` / `contD`: `remPath` / `fromJ4E` at the virtual entry
`{s with mem := M1}` (`npreV`), with the flag-1 epilogue `epiK1`, give `PostNil` at the real entry `s`.
* `ZKeep0`: `z` after the alias test, without the stack (`ZOK0`).
* `NewStk.frameE`: the new stack survives frames outside `R.rt` (copied from top's `Q.NatDiv.NewStk.frame`, to keep
  nat.div's chain out of this import closure).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

/-- `z` after the alias test (no stack at the entry): kept (with `ZOK0` if non-empty) or `nil` -/
def ZKeep0 (R : RtInv) (L : List (Nat × Nat)) (g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' : Nat)
    (M : Janus.Arm64.Memory) : Prop :=
  (zp' = zp ∧ zl' = zl ∧ zc' = zc ∧ (0 < zc → ZOK0 R L g fs sp K zp zc xp xc yp yl mp n M)) ∨
    (zp' = 0 ∧ zl' = 0 ∧ zc' = 0)

theorem zkeepV {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g fs sp K st zp zl zc xp xc yp yl mp n zp' zl' zc' : Nat}
    {M M1 : Janus.Arm64.Memory} (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' M)
    (hN : NewStk R L L1 b b1 g M1 st) (hacc : ∀ a k w, M1.accessible a k w = M.accessible a k w) :
    (zp' = zp ∧ zl' = zl ∧ zc' = zc ∧ (0 < zc → ZOK R L1 g fs sp K st zp zc xp xc yp yl mp n M1)) ∨
      (zp' = 0 ∧ zl' = 0 ∧ zc' = 0) := by
  rcases hz with ⟨a, b, c, d⟩ | h
  · exact Or.inl ⟨a, b, c, fun hc => zokV (d hc) hN hacc⟩
  · exact Or.inr h

/-- the first limb of an operand (`k ≥ 1`) is unchanged on the way to the virtual entry -/
theorem rd0_v {R : RtInv} {L : List (Nat × Nat)} {sp K p k : Nat} {M M1 : Janus.Arm64.Memory}
    (h : NE0 R L sp K p (8 * k)) (hk : 0 < k) (hLF : LiveFrame M M1 L []) (hF : MemFrame M M1 (R.rt ++ wN sp K)) :
    M1.readLE p 8 = M.readLE p 8 :=
  rd_held (held_sub h.1 (Nat.le_refl _) (by omega)) hLF hF (by have := h.2; unfold Apart at this ⊢; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem NewStk.frameE {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {M M' : Janus.Arm64.Memory} {st : Nat}
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
set_option maxHeartbeats 64000000 in
/-- `y == 1`: the `rem` path at the virtual entry -/
theorem contR (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {ns : List String} {stk : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    (hRem : NHyp.RemHyp impl R ns stk 112 needR costR)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hnf : ns.contains fn = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow bp zp' zl' zc' : Nat} {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hX : NHyp.XFacts R L xp xl xc)
    (hstk : stk ≤ K + 0x388)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Janus.Arm64.Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L []) (hrg : M1.regions = s.mem.regions)
    (hA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → M1.readLE a k = s.mem.readLE a k)
    (hfl : M1.readLE (sp + 0x3fe) 1 = 1) (hrc : M1.readLE (sp + 0x488) 8 = sp + 0x468)
    (hdw : M1.readLE (sp + 0x468) 8 = dwA) (hst : M1.readLE (sp + 0x470) 8 = st)
    (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem)
    (hna : NHyp.NoAlias zp' zc' xp xc)
    (hy : yl = 1 ∧ s.mem.readLE yp 8 = 1) (hxl0 : xl ≠ 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 remA) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h3 : S.regs 3 = BitVec.ofNat 64 zl') (h1 : S.regs 1 = BitVec.ofNat 64 zc')
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h14 : S.regs 14 = s.regs 14) (hfsS : S.fsBase = s.fsBase)
    (hdfS : S.df = s.df) (hx15 : S.xmm 15 = 0) (hmem : S.mem = M1)
    (hra : M1.readLE (sp + 0x388) 8 = remR) (hrm : M1.readLE (sp + 0x390) 8 = mp)
    (hrn : M1.readLE (sp + 0x398) 8 = n) (hrc' : M1.readLE (sp + 0x3a0) 8 = mc)
    (hbp : M1.readLE (sp + 0x490) 8 = bp) (hrv : M1.readLE (sp + 0x498) 8 = ret0)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = S.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hPV := (npreV hP hX hN hF hLF hrg hA hxl0 (by omega)).1
  have hyO : NE0 R L sp K yp (8 * yl) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
  have hg14 : S.regs 14 = BitVec.ofNat 64 g := h14.trans hP.1.2.1
  subst hmem
  refine remPath impl hap R hRem hns hnf ret0 hret F hPV hstk (MemFrame.refl _ _) rfl
    (zkeepV hz hN fun a k w => hF.accessible a k w) hna
    ⟨hy.1, by show S.mem.readLE yp 8 = 1; rw [rd0_v hyO (by omega) hLF hF]; exact hy.2⟩ hpc hSsp h0 h3 h1 h7 h6 h8 h9
    h14 hfsS hdfS hx15 hra hrm hrn hrc' hbp hrv (SlotEq.refl _ _)
    (epiK1 impl hap ret0 hret R hput F hP hxl0 hN hF hLF hfl hrc hdw hst bp _ hg14 hK')

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `y ≠ 1`: `J4` at the virtual entry -/
theorem contD (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow bp zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hX : NHyp.XFacts R L xp xl xc)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Janus.Arm64.Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L []) (hrg : M1.regions = s.mem.regions)
    (hA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → M1.readLE a k = s.mem.readLE a k)
    (hfl : M1.readLE (sp + 0x3fe) 1 = 1) (hrc : M1.readLE (sp + 0x488) 8 = sp + 0x468)
    (hdw : M1.readLE (sp + 0x468) 8 = dwA) (hst : M1.readLE (sp + 0x470) 8 = st)
    (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hEv : EvH impl R K needS costS xl yl n)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6190084) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h1 : S.regs 1 = BitVec.ofNat 64 zc') (h2 : S.regs 2 = BitVec.ofNat 64 yc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = 0#64) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h12 : S.regs 12 = BitVec.ofNat 64 yp) (h13 : S.regs 13 = BitVec.ofNat 64 mp)
    (h15 : S.regs 15 = BitVec.ofNat 64 yl)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hmem : S.mem = M1) (hsp : SpillsB M1 sp xp xl xc yp yl yc mp n mc)
    (hbp : M1.readLE (sp + 0x490) 8 = bp) (hrv : M1.readLE (sp + 0x498) 8 = ret0)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = S.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hPV := npreV hP hX hN hF hLF hrg hA hxl0 hyl0
  have hyO : NE0 R L sp K yp (8 * yl) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
  have hmO : NE0 R L sp K mp (8 * n) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hn0 : 0 < n := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hg14 : S.regs 14 = BitVec.ofNat 64 g := h14.trans hP.1.2.1
  have hz' := zkeepV hz hN fun a k w => hF.accessible a k w
  have hzJ : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L1 g fs sp K st zp zc xp xc yp yl mp n M1)) ∨
      (zp' = 0 ∧ zc' = 0) := by
    rcases hz' with ⟨a, -, c, d⟩ | ⟨a, -, c⟩
    · exact Or.inl ⟨a, c, d⟩
    · exact Or.inr ⟨a, c⟩
  have ey := rd0_v hyO (by omega) hLF hF
  have em := rd0_v hmO hn0 hLF hF
  refine fromJ4E impl hap R H ret0 hret F hPV.1 hPV.2 hzJ hxl0 hyl0
    (by show ¬(yl = 1 ∧ M1.readLE yp 8 = 1); rw [ey]; exact hy1)
    (by show ¬(n = 1 ∧ M1.readLE mp 8 = 1); rw [em]; exact hm1) hEv
    S M1 hpc hSsp h0 h1 h2 h7 h6 h8 h9 h10 h11 h12 h13 h15 h14 hfs hdf hx15 hmem (MemFrame.refl _ _) rfl hsp hbp hrv
    (SlotEq.refl _ _)
    (epiK1 impl hap ret0 (retAddr_down hret) R hput F hP hxl0 hN hF hLF hfl hrc hdw hst bp _ hg14 hK')

end FvModexp.Amd64.ExpN
