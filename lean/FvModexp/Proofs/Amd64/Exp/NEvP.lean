import FvModexp.Proofs.Amd64.Exp.NP2P
import FvModexp.Proofs.Amd64.Exp.NPowE
import FvModexp.Proofs.Amd64.Exp.NCallE
import FvModexp.Proofs.Amd64.Exp.EvStmt

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): the `expNNEven` path (agent expmc s73; twin of `Arm64.ExpN.evPath`)

`evPath`: from the `isPow2` loop head `powH` (after the make, `RSP = sp + 0x390`) for an even `m` that is not a power
of two: `powAllE` → the call (`EvK`: `y`, `m` stored as stack arguments) → asm's `ExpEven.EvenSum` (a `Summary` of
`LibNE`, `callCE`) → the epilogue (`EpiK`, lifted). The callee's precondition comes from `NPre` (`cpre_at` with the
operands `x, y, m`; `2 ≤ y` from `¬(len y = 1 ∧ y[0] = 1)`; `XG` at the call memory as `p2Path`'s); its need/cost are
bounded by the slow slot's (`hnE`, `hcE`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the power-of-two path from the `isPow2` loop head (`RSP = sp + 0x390`) to expNN's return -/
theorem evPath (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {stk : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hES : ExpEven.EvenSum impl R stk 0x70 needE costE)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hX : NHyp.XFacts R L xp xl xc) (hstk : stk ≤ K + 0x388)
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hnp : ¬∃ k, natVal s.mem mp n = 2 ^ k) (hm0 : s.mem.readLE mp 8 % 2 = 0)
    (hnE : needE xl yl n ≤ needS xl yl n) (hcE : ∀ l, costE l xl yl n ≤ costS l xl yl n)
    (hpc : S.rip = BitVec.ofNat 64 powH) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (a0 : S.regs 0 = BitVec.ofNat 64 zq) (a1 : S.regs 1 = BitVec.ofNat 64 zcq) (a11 : S.regs 11 = BitVec.ofNat 64 n)
    (a7 : S.regs 7 = BitVec.ofNat 64 st) (a6 : S.regs 6 = BitVec.ofNat 64 xp) (a8 : S.regs 8 = BitVec.ofNat 64 xl)
    (a9 : S.regs 9 = BitVec.ofNat 64 xc) (a12 : S.regs 12 = BitVec.ofNat 64 yp)
    (a15 : S.regs 15 = BitVec.ofNat 64 yl) (a2 : S.regs 2 = BitVec.ofNat 64 yc) (a3 : S.regs 3 = BitVec.ofNat 64 n)
    (a13 : S.regs 13 = BitVec.ofNat 64 mp) (a10 : S.regs 10 = 0#64)
    (hzs : S.mem.readLE (sp + 0x438) 8 = zq) (hSn : S.mem.readLE (sp + 0x4c0) 8 = n)
    (hSmc : S.mem.readLE (sp + 0x4c8) 8 = mc)
    (h14 : S.regs 14 = s.regs 14) (hfsS : S.fsBase = s.fsBase) (hdfS : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hbp : S.mem.readLE (sp + 0x490) 8 = bp) (hrv : S.mem.readLE (sp + 0x498) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, hK1, hK2, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    hn, hn128, hnmc, hmc, hmO, hma, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, hx48, hxN, hxl, hxlc, hxc, -, -, -, -,
    -, ⟨op, hOne, hSA⟩, hst0, hst48, hsok, hstw, -, -, harr, hc0, -, -, -, -, -, -, -, hnS, -, hbud, -, -, hXG⟩ := hP'
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hwrt, -, -, hLs, -⟩ := hce
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hrw := rw_of hK0 hwrt
  have hzq := hZ.2.2.2.2.2.2.2.2.2.2
  have hnz := hZ.2.2.2.2.2.2.2.2.2.1
  have hzc40 := hZ.2.2.2.2.2.2.2.1.1
  have hF0 := hZ.1
  have hLF0 := hZ.2.1
  -- the modulus words
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  have hmNS : NatNorm S.mem mp n := by
    rcases hmN with h | h
    · exact Or.inl h
    · right; rw [rd_held (held_sub hmO.1 (by omega) (by omega)) hLF0 hF0 (by have := hmO.2.1; unfold Apart at this ⊢; omega)]; exact h
  have hnpS : ¬∃ k, natVal S.mem mp n = 2 ^ k := by rw [hrdm]; exact hnp
  have hSs : (S.regs 4).toNat = sp + 0x390 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  refine powAllE impl ret0 hret _ S.regs S.fsBase S.df (S.xmm 15) (sp + 0x498) mp n S.mem
    (by omega) (by omega) (by rw [hF0.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    hm48 (by rw [hF0.accessible]; exact hma) hn hmNS hnpS
    (by rw [show sp + 0x498 - 0x60 = sp + 0x438 by omega, hzs, a0, BitVec.toNat_ofNat]; omega) a3
    (by rw [hSsp]; exact congrArg _ (by omega)) a13 ?_ (n - 1) 0 S (by omega) hn (fun j hj => absurd hj (by omega))
    hpc (fun _ _ => rfl) (by rw [a10]) rfl rfl rfl rfl
  intro S' M' e_rip e4 e0 e1 e3 e7 e6 e8 e9 e14 efs edf ex15 emem hMF hrg' hra' hy0 hy1' hy2 hm0' hm1' hm2'
  subst emem
  have hws : ∀ a k, Outside a k (wN sp K) → Outside a k [(sp + 0x498 - 0x110, sp + 0x498 - 0xd8)] := fun a k ho => by
    simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hLs1 : LiveSep L1 [(sp + 0x498 - 0x110, sp + 0x498 - 0xd8)] := fun r hr => by
    have := (hZ.2.2.2.1.liveSep hLs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 0x510 - (sp - K) = K + 0x510 by omega]; exact hwrt)) r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hZ' := zm_frame hZ hMF hrg' hws (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hwrt.of_sub (by omega) (by omega)) hLs1 hstw
  obtain ⟨hF0', hLF0', hrg1, hx1, hb1, hmk, hinv1, hZQ, hZA, -, -⟩ := hZ'
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S'.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0' hF0' (by unfold Apart at hstw ⊢; omega)
  have ew : stW S'.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S'.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S'.mem st = stCap s.mem st := rdh 16 (by omega)
  have hrdx : natVal S'.mem xp xl = natVal s.mem xp xl :=
    rd_held (held_sub hxO.1 (Nat.le_refl _) (by omega)) hLF0' hF0' (by have := hxO.2.1; unfold Apart at this ⊢; omega)
  have hrdy : natVal S'.mem yp yl = natVal s.mem yp yl := rd_held hyO.1 hLF0' hF0' hyO.2.1
  have hrdm' : natVal S'.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0' hF0' hmO.2.1
  have hS'sp : S'.regs 4 = BitVec.ofNat 64 (sp + 0x388) := by rw [e4]; exact congrArg _ (by omega)
  have hS's : (S'.regs 4).toNat = sp + 0x388 := by rw [hS'sp, BitVec.toNat_ofNat]; omega
  have kf : ∀ a k, sp + 0x3f8 ≤ a → S'.mem.readLE a k = S.mem.readLE a k := fun a k ha =>
    hMF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hOne' := natOne_at hOne hSA hF0' hLF0' hx1 hS's hstk hK0 hZA (by omega) ew el ec
  have hCP : NHyp.CPre R b1 L1 stk 0x70 zq n zcq st [(xp, xl), (yp, yl), (mp, n)] (needE xl yl n)
      (costE (stLen S'.mem st) xl yl n) S' :=
    cpre_at hP hF0' hLF0' hrg1 hx1 hinv1 hS'sp (e14.trans (h14.trans hs14))
      (by rw [efs, hfsS]; exact hsfs) hstk hZQ hnz
      (fun p k hpk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpk
        rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩))
      (by omega) (by have := hcE (stLen S'.mem st); rw [el] at this ⊢; omega)
  have hS := hES b1 L1 zq n zcq st xp xl xc yp yl yc mp n mc
  refine callCE impl hap ret0 hret F (bp := bp) hs hK0 (by omega) hA0 hLs hrw hsok hstw hF0' hLF0' hx1
    hb1 hZA hstk (e14.trans h14) (efs.trans hfsS) (edf.trans hdfS) ?_ ?_
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hS e_rip hS'sp
    (by rw [← show sp + 0x498 - 0x110 = sp + 0x388 by omega]; exact hra') (ex15.trans hx15)
    ⟨ex15.trans hx15, edf.trans (hdfS.trans hsdf), by rw [e0, a0], by rw [e3, a11], by rw [e1, a1], by rw [e7, a7],
      by rw [e6, a6], by rw [e8, a8], by rw [e9, a9], ?_, ?_, ⟨hCP, ?_, ?_, ?_, ?_, hxl, by omega, hst0, hnmc, hmc,
        ?_, ⟨op, hOne'⟩⟩, hzq, by omega, by omega, ?_, hX.ext hx1, ?_, ?_⟩
    (fun s' h => ⟨⟨h.1.1, h.1.2.2.1, h.1.2.2.2⟩, h.2.1, h.2.2.1, cpostG_of hzq h.2⟩)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1)
    (by rw [hF0'.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    (by rw [kf _ _ (by omega)]; exact hbp) (by rw [kf _ _ (by omega)]; exact hrv)
    (hsl.of_rd fun a k hs => kf a k (by unfold Slot at hs; omega)) (by rw [e14]; exact hEk)
  · rw [hrdx, hrdy, hrdm']
  · have := hcE (stLen s.mem st); rw [el]; unfold NCost; omega
  · simp only [NHyp.StkArg, hS's]
    refine ⟨?_, ?_, ?_⟩
    · rw [show sp + 0x388 + 0 + 8 = sp + 0x498 - 0x108 by omega, hy0, a12, BitVec.toNat_ofNat]; omega
    · rw [show sp + 0x388 + 0 + 16 = sp + 0x498 - 0x100 by omega, hy1', a15, BitVec.toNat_ofNat]; omega
    · rw [show sp + 0x388 + 0 + 24 = sp + 0x498 - 0xf8 by omega, hy2, a2, BitVec.toNat_ofNat]; omega
  · simp only [NHyp.StkArg, hS's]
    refine ⟨?_, ?_, ?_⟩
    · rw [show sp + 0x388 + 24 + 8 = sp + 0x498 - 0xf0 by omega, hm0', a13, BitVec.toNat_ofNat]; omega
    · rw [show sp + 0x388 + 24 + 16 = sp + 0x498 - 0xe8 by omega, hm1', show sp + 0x498 + 0x28 = sp + 0x4c0 by omega]; exact hSn
    · rw [show sp + 0x388 + 24 + 24 = sp + 0x498 - 0xe0 by omega, hm2', show sp + 0x498 + 0x30 = sp + 0x4c8 by omega]; exact hSmc
  · rw [hrdx]; exact val_pos hxN hxl0
  · rw [hrdy]; exact val_two hyN hyl0 hy1
  · rw [hrdm']; exact val_pos hmN (by omega)
  · rw [hrdm', val_mod2 hn]; exact hm0
  · exact (hCP.2.2.2.2.2.2.1.2.2 (by omega)).1
  · have hra2 := hra'; rw [show sp + 0x498 - 0x110 = sp + 0x388 by omega] at hra2
    rw [hS's, hra2]; decide
  · obtain ⟨xa, xn, xd, xacc, xst, xfr⟩ := hXG
    refine ⟨xa, by rw [hOne'.1.1, ← hOne.1]; exact xn, by rw [hF0'.accessible]; exact xd,
      by rw [hF0'.accessible]; exact xacc, xst, ?_⟩
    simp only [W4En.free, ew, el, ec] at xfr ⊢; exact xfr
  · have := hxO.2.1
    simp only [win, hS's, outside_cons, outside_nil, and_true]; unfold Apart at this; omega

end FvModexp.Amd64.ExpN
