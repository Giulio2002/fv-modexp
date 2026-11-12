import FvModexp.Proofs.Arm64.Exp.NNilC
import FvModexp.Proofs.Arm64.Exp.NMidE

/-!
# `nat.expNN` (arm64), `stk == nil`: the downstream chain at the virtual entry, on `LibNE` (every modulus)

`contRE` = `contR` lifted (`liftNE`); `contDE` = `contD` with `fromJ5E` (no `noEven` restriction). `EvH`: the
`expNNEven` summary (infra's `ExpEven.EvenSum`) with its stack/need/cost bounded by expNN's slow slot.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- the even call's callee summary, its stack within expNN's callee window, need/cost within the slow slot's -/
def EvH (impl : List Segment) (R : RtInv) (K : Nat) (needS : Nat → Nat → Nat → Nat)
    (costS : Nat → Nat → Nat → Nat → Nat) (xl yl n : Nat) : Prop :=
  ∃ (stkE : Nat) (needE : Nat → Nat → Nat → Nat) (costE : Nat → Nat → Nat → Nat → Nat),
    ExpEven.EvenSum impl R stkE 112 needE costE ∧ stkE ≤ K + 1056 ∧ needE xl yl n ≤ needS xl yl n ∧
      ∀ l, costE l xl yl n ≤ costS l xl yl n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `contR` on `LibNE` -/
theorem contRE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {ns : List String} {stk : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    (hRem : NHyp.RemHyp impl R ns stk 112 needR costR)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hn11 : ns.contains Extracted.seg11.name = false)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow f29 zp' zl' zc' : Nat} {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow s)
    (hstk : stk ≤ K + 1056)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L []) (hrg : M1.regions = s.mem.regions)
    (h1182 : M1.readLE (sp + 1182) 1 = 1) (h1296 : M1.readLE (sp + 1296) 8 = sp + 1272)
    (h1272 : M1.readLE (sp + 1272) 8 = dwA) (h1280 : M1.readLE (sp + 1280) 8 = st)
    (hz : ZKeep0 R L g sp K zp zl zc xp xl yp yl mp n zp' zl' zc' s.mem)
    (hna : NHyp.NoAlias zp' zc' xp xc)
    (hy : yl = 1 ∧ s.mem.readLE yp 8 = 1) (hxl0 : xl ≠ 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 remA) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h1 : S.regs 1 = BitVec.ofNat 64 zl') (h2 : S.regs 2 = BitVec.ofNat 64 zc')
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 mp) (h8 : S.regs 8 = BitVec.ofNat 64 n)
    (h9 : S.regs 9 = BitVec.ofNat 64 mc) (h28 : S.regs 28 = s.regs 28) (h30 : S.regs 30 = BitVec.ofNat 64 1787296)
    (hmem : S.mem = M1) (h29v : M1.readLE (sp + 1048) 8 = f29) (h30v : M1.readLE (sp + 1056) 8 = ret0)
    (hK' : ∀ s'' : State, s''.sp = BitVec.ofNat 64 (sp + 1312) → s''.regs 29 = BitVec.ofNat 64 f29 →
      s''.regs 18 = S.regs 18 → s''.regs 28 = S.regs 28 →
      PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) :=
  liftNE impl hap (contR impl hap R hput hRem hns hn11 ret0 (retAddr_down hret) F hP hstk hN hF hLF hrg
    h1182 h1296 h1272 h1280 hz hna hy hxl0 S hpc hSsp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h28 h30 hmem h29v h30v hK')

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `contD` on `LibNE`, every modulus (`fromJ5E`; the even call's need/cost: `EvH`) -/
theorem contDE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow f29 zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L []) (hrg : M1.regions = s.mem.regions)
    (h1182 : M1.readLE (sp + 1182) 1 = 1) (h1296 : M1.readLE (sp + 1296) 8 = sp + 1272)
    (h1272 : M1.readLE (sp + 1272) 8 = dwA) (h1280 : M1.readLE (sp + 1280) 8 = st)
    (hz : ZKeep0 R L g sp K zp zl zc xp xl yp yl mp n zp' zl' zc' s.mem)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hev : EvH impl R K needS costS xl yl n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1787348) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h2 : S.regs 2 = BitVec.ofNat 64 zc')
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 mc) (h13 : S.regs 13 = 0#64)
    (h28 : S.regs 28 = s.regs 28) (hmem : S.mem = M1)
    (hsp : SpillsB M1 sp xp xl xc yp yl yc mp n mc)
    (h29v : M1.readLE (sp + 1048) 8 = f29) (h30v : M1.readLE (sp + 1056) 8 = ret0)
    (hK' : ∀ s'' : State, s''.sp = BitVec.ofNat 64 (sp + 1312) → s''.regs 29 = BitVec.ofNat 64 f29 →
      s''.regs 18 = S.regs 18 → s''.regs 28 = S.regs 28 →
      PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  obtain ⟨stkE, needE, costE, hEv, hstkE, hnE, hcE⟩ := hev
  have hPV := npreV hP hN hF hLF hrg hxl0 hyl0
  have hyO : NE0 R L sp K yp (8 * yl) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
  have hmO : NE0 R L sp K mp (8 * n) := hP.2.2.2.2.2.2.2.2.2.2.1
  have hn0 : 0 < n := hP.2.2.2.2.2.2.1
  have hg28 : S.regs 28 = BitVec.ofNat 64 g := h28.trans hP.1.2.1
  have hz' := zkeepV hz hN fun a k w => hF.accessible a k w
  have hzJ : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L1 g sp K st zp zc xp xl yp yl mp n M1)) ∨
      (zp' = 0 ∧ zc' = 0) := by
    rcases hz' with ⟨a, -, c, d⟩ | ⟨a, -, c⟩
    · exact Or.inl ⟨a, c, d⟩
    · exact Or.inr ⟨a, c⟩
  have ey := rd0_v hyO (by omega) hLF hF
  have em := rd0_v hmO hn0 hLF hF
  refine fromJ5E impl hap R H hEv hstkE ret0 hret F hPV hzJ hxl0 hyl0 (by show ¬(yl = 1 ∧ M1.readLE yp 8 = 1); rw [ey]; exact hy1)
    (by show ¬(n = 1 ∧ M1.readLE mp 8 = 1); rw [em]; exact hm1) hnE hcE
    S M1 hpc hSsp h0 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h28 hmem (MemFrame.refl _ _) rfl hsp h29v h30v
    (SlotEq.refl _ _) (epiK1 impl hap ret0 (retAddr_down hret) R hput F hP hxl0 hN hF hLF h1182 h1296 h1272 h1280 f29 _ _ hg28 hK')

end FvModexp.Arm64.ExpN
