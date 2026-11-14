import FvModexp.Proofs.Amd64.Exp.NOddP
import FvModexp.Proofs.Amd64.Exp.NP2P

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): from `J5` (`0x5e750b`, after `z = z.make(len m)`) to expNN's return (agent expmc s72; twin
of the `tgt` part of `Arm64.ExpN.fromJ5`)

`fromJ5`: `NDisp.disp`, then the `expNNSlow` / `expNNOdd` / `expNNPowerOfTwo` paths (`slowPath`, `oddPath`,
`p2Path`) from a `J5` state with the make context `ZM` (the dispatch's stores are a frame inside `wN`: `zm_frame`).
The modulus is odd or a power of two (`NoEvenB`), so the `isPow2` loop always finds `logM`. `DHyps` = the callee
premises of the three paths and of the make (`NMidM`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- the callee premises of the make and the dispatch paths -/
structure DHyps (impl : List Amd64.Segment) (R : RtInv) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needS needP : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (nsD : List String) (stkD : Nat) (nsS : List String) (stkS : Nat) (nsP : List String) (stkP : Nat) : Prop where
  mkN : MakesliceLiveContract64 (LibN.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R
  clr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
    (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R
  mv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R
  mkO : MakesliceLiveContract64 (Extracted.program.ofImpl impl)
    (Extracted.program.contractAddr "runtime.makeslice") 4096 R
  gr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl)
    (Extracted.program.contractAddr "runtime.growslice") 4096 R
  wb : WbLiveContract64 (Extracted.program.ofImpl impl)
    (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2
  div : ExpHyp.DivHypL impl R nsD stkD 112 costF
  hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true
  hnsW4 : nsD.contains W4Loop.fn = false
  hnsW2 : nsD.contains W2Loop.fn = false
  hKD : stkD + 0x80 ≤ K
  slow : NHyp.SlowHyp impl R nsS stkS 112 needS costS
  hnsS : ∀ x, nsS.contains x = true → LibN.names.contains x = true
  hnfS : nsS.contains fn = false
  hKS : stkS ≤ K + 0x388
  p2 : NHyp.P2Hyp impl R nsP stkP 112 needP costP
  hnsP : ∀ x, nsP.contains x = true → LibN.names.contains x = true
  hnfP : nsP.contains fn = false
  hKP : stkP ≤ K + 0x388

/-- the modulus is odd or a power of two (hidden from `omega`) -/
def NoEvenB (M : Memory) (mp n : Nat) : Prop := natVal M mp n % 2 = 1 ∨ ∃ k, natVal M mp n = 2 ^ k

/-- the registers at `J5` -/
@[reducible] def J5S (D : State) (zq zcq st xp xl xc yp yl yc mp n : Nat) : Prop :=
  D.regs 0 = BitVec.ofNat 64 zq ∧ D.regs 1 = BitVec.ofNat 64 zcq ∧ D.regs 7 = BitVec.ofNat 64 st ∧
  D.regs 6 = BitVec.ofNat 64 xp ∧ D.regs 8 = BitVec.ofNat 64 xl ∧ D.regs 9 = BitVec.ofNat 64 xc ∧
  D.regs 10 = 0#64 ∧ D.regs 12 = BitVec.ofNat 64 yp ∧ D.regs 15 = BitVec.ofNat 64 yl ∧
  D.regs 2 = BitVec.ofNat 64 yc ∧ D.regs 3 = BitVec.ofNat 64 n ∧ D.regs 11 = BitVec.ofNat 64 n ∧
  D.regs 13 = BitVec.ofNat 64 mp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `J5` with the make context `ZM` to expNN's return -/
theorem fromJ5 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp : Nat} {s : State}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hX : NHyp.XFacts R L xp xl xc)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hev : NoEvenB s.mem mp n)
    {M1 : Memory} {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem M1 L1 b1 zq zcq mk)
    (D : State) (hpc : D.rip = BitVec.ofNat 64 j5A) (hDsp : D.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (hJ : J5S D zq zcq st xp xl xc yp yl yc mp n)
    (h14 : D.regs 14 = s.regs 14) (hfs : D.fsBase = s.fsBase) (hdf : D.df = s.df) (hx15 : D.xmm 15 = 0)
    (hm : D.mem = M1) (hmc : M1.readLE (sp + 0x4c8) 8 = mc)
    (hbp : M1.readLE (sp + 0x490) 8 = bp) (hrv : M1.readLE (sp + 0x498) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq M1 M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (D.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) D (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨-, -, -, -, -, -, -, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    hn, hn128, -, -, hmO, hma, hm48, -, hyO, hya, hy48, -, hyl, hyc, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hst48, -, hstw, -⟩ := hP'
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hwrt, -, -, hLs, -⟩ := hce
  obtain ⟨j0, j1, j7, j6, j8, j9, j10, j12, j15, j2, j3, j11, j13⟩ := hJ
  have hZ' := hZ
  obtain ⟨hF1, hLF1, -, hx1, -, -, -, -, -, -, hzq⟩ := hZ'
  have hW1 : Outside (sp - K) (sp + 0x490 - (sp - K)) R.rt :=
    wN_rt (rw_of hK0 hwrt) (sp - K, sp + 0x490) (by simp [wN])
  have hLsW : LiveSep L1 [(sp - K, sp + 0x510)] := hx1.liveSep hLs (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only
    rw [show sp + 0x510 - (sp - K) = K + 0x510 by omega]; exact hwrt)
  -- the dispatch frames (inside `[sp - K, sp + 0x490)`, apart from the epilogue slots)
  have frC : ∀ {M' : Memory}, MemFrame M1 M' [(sp + 0x498 - 0x110, sp + 0x498 - 0xd8),
      (sp + 0x498 - 0x98, sp + 0x498 - 0x90)] → M'.regions = M1.regions →
      ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem M' L1 b1 zq zcq mk ∧
      M'.readLE (sp + 0x490) 8 = bp ∧ M'.readLE (sp + 0x498) 8 = ret0 ∧ SlotEq M' M0 (sp + 0x498) :=
    fun {M'} hMF hrg' => by
      refine ⟨zm_frame hZ hMF hrg' (fun a k ho => by
          simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact hW1.of_sub (by omega) (by omega))
        (fun q hq => by
          have := hLsW q hq
          simp only [outside_cons, outside_nil, and_true] at this ⊢; omega) hstw,
        by rw [hMF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hbp,
        by rw [hMF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hrv,
        hsl.of_frame hMF fun a k hs => by
          unfold Slot at hs; simp only [outside_cons, outside_nil, and_true]; omega⟩
  have frP : ∀ {M' : Memory}, MemFrame M1 M' [(sp + 0x498 - 0x98, sp + 0x498 - 0x90),
      (sp + 0x498 - 0x60, sp + 0x498 - 0x58)] → M'.regions = M1.regions →
      ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem M' L1 b1 zq zcq mk ∧
      M'.readLE (sp + 0x490) 8 = bp ∧ M'.readLE (sp + 0x498) 8 = ret0 ∧ SlotEq M' M0 (sp + 0x498) :=
    fun {M'} hMF hrg' => by
      refine ⟨zm_frame hZ hMF hrg' (fun a k ho => by
          simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact hW1.of_sub (by omega) (by omega))
        (fun q hq => by
          have := hLsW q hq
          simp only [outside_cons, outside_nil, and_true] at this ⊢; omega) hstw,
        by rw [hMF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hbp,
        by rw [hMF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hrv,
        hsl.of_frame hMF fun a k hs => by
          unfold Slot at hs; simp only [outside_cons, outside_nil, and_true]; omega⟩
  have hrd1 : ∀ {a k : Nat}, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - K) (K + 0x510) →
      M1.readLE a k = s.mem.readLE a k := fun hH hw => rd_held hH hLF1 hF1 hw
  have hm01 : M1.readLE mp 8 = s.mem.readLE mp 8 :=
    hrd1 (a := mp) (k := 8) (held_sub hmO.1 (by omega) (by omega)) (by have := hmO.2.1; unfold Apart at this ⊢; omega)
  have hDs : D.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := hDsp.trans (congrArg _ (by omega))
  refine disp impl ret0 hret _ (sp + 0x498) yp yl yc mp n mc M1 (by omega) (by omega)
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hya (by omega) (by omega))
    (by have := hyO.2.1; unfold Apart at this; omega)
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hma (by omega) (by omega))
    (by have := hmO.2.1; unfold Apart at this; omega)
    (by rw [show sp + 0x498 + 0x30 = sp + 0x4c8 by omega]; exact hmc)
    D hpc hDs j10 j12 j15 j2 j3 j11 j13 hm ?KS ?KO ?KP
  case KS =>
    intro _ _ S' M' e_rip e4 e0 e1 e3 e7 e6 e8 e9 e14 efs edf ex15 emem hMF hrg' hra q0 q1 q2 q3 q4 q5
    subst emem
    obtain ⟨hZ2, f1, f2, f3⟩ := frC hMF hrg'
    exact slowPath impl hap R H.slow H.hnsS H.hnfS ret0 hret F hP hX H.hKS hZ2 hxl0 hyl0 hy1 e_rip
      (e4.trans (congrArg _ (by omega)))
      ⟨e0.trans j0, e3, e1.trans j1, e7.trans j7, e6.trans j6, e8.trans j8, e9.trans j9,
        by rw [show sp + 0x390 = sp + 0x498 - 0x108 by omega]; exact q0,
        by rw [show sp + 0x398 = sp + 0x498 - 0x100 by omega]; exact q1,
        by rw [show sp + 0x3a0 = sp + 0x498 - 0xf8 by omega]; exact q2,
        by rw [show sp + 0x3a8 = sp + 0x498 - 0xf0 by omega]; exact q3,
        by rw [show sp + 0x3b0 = sp + 0x498 - 0xe8 by omega]; exact q4,
        by rw [show sp + 0x3b8 = sp + 0x498 - 0xe0 by omega]; exact q5⟩
      (e14.trans h14) (efs.trans hfs) (edf.trans hdf) (ex15.trans hx15)
      (by rw [show sp + 0x388 = sp + 0x498 - 0x110 by omega]; exact hra) f1 f2 f3 (by rw [e14]; exact hEk)
  case KO =>
    intro _ hodd S' M' e_rip e4 e0 e1 e3 e7 e6 e8 e9 e14 efs edf ex15 emem hMF hrg' hra q0 q1 q2 q3 q4 q5
    subst emem
    obtain ⟨hZ2, f1, f2, f3⟩ := frC hMF hrg'
    exact oddPath impl hap R H.clr H.mv H.mkO H.gr H.wb nsD stkD H.div H.hnsD H.hnsW4 H.hnsW2 ret0 hret F H.hKD
      hP hZ2 hxl0 hyl0 (by rw [← hm01]; exact hodd) hm1 e_rip (e4.trans (congrArg _ (by omega)))
      ⟨e0.trans j0, e3, e1.trans j1, e7.trans j7, e6.trans j6, e8.trans j8, e9.trans j9,
        by rw [show sp + 0x390 = sp + 0x498 - 0x108 by omega]; exact q0,
        by rw [show sp + 0x398 = sp + 0x498 - 0x100 by omega]; exact q1,
        by rw [show sp + 0x3a0 = sp + 0x498 - 0xf8 by omega]; exact q2,
        by rw [show sp + 0x3a8 = sp + 0x498 - 0xf0 by omega]; exact q3,
        by rw [show sp + 0x3b0 = sp + 0x498 - 0xe8 by omega]; exact q4,
        by rw [show sp + 0x3b8 = sp + 0x498 - 0xe0 by omega]; exact q5⟩
      (e14.trans h14) (efs.trans hfs) (edf.trans hdf) (ex15.trans hx15)
      (by rw [show sp + 0x388 = sp + 0x498 - 0x110 by omega]; exact hra) f1 f2 f3 (by rw [e14]; exact hEk)
  case KP =>
    intro _ hev0 S' M' e_rip e4 e0 e1 e2 e3 e7 e6 e8 e9 e10 e11 e12 e13 e15 e14 efs edf ex15 emem hMF hrg' hz60
    subst emem
    obtain ⟨hZ2, f1, f2, f3⟩ := frP hMF hrg'
    have hm0 : s.mem.readLE mp 8 % 2 = 0 := by rw [← hm01]; exact hev0
    have hpow : ∃ k, natVal s.mem mp n = 2 ^ k := by
      rcases (hev : natVal s.mem mp n % 2 = 1 ∨ ∃ k, natVal s.mem mp n = 2 ^ k) with h | h
      · rw [val_mod2 hn] at h; omega
      · exact h
    exact p2Path impl hap R H.p2 H.hnsP H.hnfP ret0 hret F hP hX H.hKP hZ2 hxl0 hyl0 hpow hm0 e_rip (e4.trans hDsp)
      (e0.trans j0) (e1.trans j1) (e11.trans j11) (e7.trans j7) (e6.trans j6) (e8.trans j8) (e9.trans j9)
      (e12.trans j12) (e15.trans j15) (e2.trans j2) (e3.trans j3) (e13.trans j13) e10
      (by rw [show sp + 0x438 = sp + 0x498 - 0x60 by omega, hz60, j0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hzq)
      (e14.trans h14) (efs.trans hfs) (edf.trans hdf) (ex15.trans hx15) f1 f2 f3 (by rw [e14]; exact hEk)

end FvModexp.Amd64.ExpN
