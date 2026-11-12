import FvModexp.Proofs.Arm64.Exp.NMkP
import FvModexp.Proofs.Arm64.Exp.NDisp
import FvModexp.Proofs.Arm64.Exp.OddFun
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.expNN` (arm64): the odd-modulus path — `z.expNNOdd(stk, x, y, m)` (nat.go:708-710) to expNN's return

From `expNNOdd`'s entry (`NDisp.disp`'s `KO`, `m[0]` odd, after the make: context `ZM`): `ExpOdd.ens` (on `LibOdd`,
which leaves out `nat.expNN`) with `ExpOdd.Pre` at the entry (`opre_at`: `OPre`'s window `[sp - K, sp + 1168)` lies in
expNN's `[sp - K, sp + 1432)`, same `sp`), `ExpOdd.Post` as a `CPostG` (`cpostG_odd`), then `callC`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
/-- an entry operand (`NE` at `s.mem`, `L`) as an `expNNOdd` operand (`OE` at the callee entry, `L1`) -/
theorem oe_at {R : RtInv} {L L1 : List (Nat × Nat)} {sp K st a k : Nat} {M0 M : Memory} (hO : NE R L sp K st M0 a k)
    (hx : LiveExt R L L1) (ew : stW M st = stW M0 st) (el : stLen M st = stLen M0 st) (ec : stCap M st = stCap M0 st) :
    ExpOdd.OE R L1 sp K st M a k := by
  obtain ⟨hH, hw, hst, hfr⟩ := hO
  refine ⟨hx.held hH, by unfold Apart at hw ⊢; omega, hst, ?_⟩
  show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
  rw [ew, el, ec]; exact hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `ExpOdd.OPre` at `expNNOdd`'s entry (`S.sp = sp + 1056`) from `NPre` and the make's context -/
theorem opre_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s S : State} {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hZ : ZM R b L g sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) :
    ExpOdd.OPre R b1 L1 K g sp st zq zcq xp xl xc yp yl mp n mc S := by
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩, hK20, hgl, hro, hty, -,
    hn, hn128, hnm, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, -, hxO, hxa, hx48, hxN, hxl, hxp, hxc, -, -,
    -, -, hgO, -, -, -, hsok, hstw, hstg, harr, hc0, hwbf, hwbA, hstf, -, hrnd, -, -, -, -, -⟩ := hP
  obtain ⟨hF, hLF, hrg, hx, -, -, hinv1, ⟨hzc40, hzL, hzA⟩, -, hnz, hzq⟩ := hZ
  have hSs : S.sp.toNat = sp + 1056 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  simp only [outside_cons] at hgo
  have hgw : Outside (g + 16) 8 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; omega
  have hgM : S.mem.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 :=
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgo.2, hgw⟩)
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have nrm : ∀ {p k : Nat}, NE R L sp K st s.mem p (8 * k) → NatNorm s.mem p k → NatNorm S.mem p k := by
    intro p k hO hN
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact Or.inl hk0
    rcases hN with h0 | h1
    · exact Or.inl h0
    · right
      rw [rd_held (held_sub hO.1 (by omega) (by omega)) hLF hF (by have := hO.2.1; unfold Apart at this ⊢; omega)]
      exact h1
  -- the globals
  have hgl' : RunIface.Globals R S.mem [(sp - K, sp + 1168)] := by
    obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw', hwbacc, hwbrt, hwbw⟩ := hgl
    have hgA : Outside RunIface.gA 32 (R.rt ++ wN sp K) := by
      simp only [wN, outside_append, outside_cons, outside_nil, and_true] at hgw' ⊢
      exact ⟨hgrt, by omega, by omega⟩
    have hrd : ∀ k, k + 8 ≤ 32 → S.mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 := fun k hk =>
      hF.readLE _ _ (hgA.of_sub (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, (hF.accessible _ _ _).trans hgacc, hgrt, ?_,
      (hF.accessible _ _ _).trans hwbacc, hwbrt, ?_⟩
    · rw [e8, hrd 8 (by omega), ← e8]; exact h40
    · rw [e16, hrd 16 (by omega), ← e16]; exact h12
    · rw [e24, hrd 24 (by omega), ← e24]; exact h80
    · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
      show S.mem.readLE RunIface.gA 8 = 40; rw [this]; exact h40'
    · simp only [outside_cons, outside_nil, and_true] at hgw' ⊢; omega
    · simp only [outside_cons, outside_nil, and_true] at hwbw ⊢; omega
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hzA (by omega)
  obtain ⟨zl8, zlH, zlacc, zl48⟩ := hzL (by omega)
  refine ⟨⟨hSsp, h28, hg1, by rw [hF.accessible]; exact hg2, by rw [hgM]; exact hg3,
      ⟨by omega, hgo.2⟩, hal, hK, hK', by omega,
      by rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega),
      LiveSep.sub_win_rt hwrt (Nat.le_refl _) (by omega) (by omega), ?_,
      dataLoaded_frame hd hrg hro hF (fun r hr _ => by
        simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)), hsv⟩,
    hK20, hgl', hro, hty, hn, hn128, hnm, hmc,
    oe_at hmO hx ew el ec, by rw [hF.accessible]; exact hma, hm48, nrm hmO hmN,
    oe_at hyO hx ew el ec, by rw [hF.accessible]; exact hya, hy48, nrm hyO hyN, by omega, by omega,
    oe_at hxO hx ew el ec, by rw [hF.accessible]; exact hxa, hx48, nrm hxO hxN, by omega, hxl, hxp, hxc,
    hzq, hzc40, by unfold Apart at z1 ⊢; omega, fun _ => ⟨⟨zlH, by unfold Apart at z1 ⊢; omega, z3, z4⟩, zlacc, zl48,
      zl8, by unfold Apart at z2 ⊢; omega, z8, z7⟩,
    oe_at hgO hx ew el ec, stkOK_hdr hsok hF ew el ec hx, by unfold Apart at hstw ⊢; omega, hstg, ?_,
    by rw [ec, ew]; exact hc0, by rw [hF.accessible]; exact hwbf, hwbA, ?_, ?_, hinv1⟩
  · refine hx.liveSep (LiveSep.sub_win hLs (Nat.le_refl _) (by omega)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)
  · rw [ec, ew]; intro hc
    obtain ⟨a1, a2⟩ := harr hc
    exact ⟨by unfold Apart at a1 ⊢; omega, a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hstf
  · rw [el]
    have := FvModexp.Arm64.ExpW4.rnd_ge (23 * n)
    omega

/-- `ExpOdd.Post` (callee entry `S`) as the `CPostG` `post_call` consumes (`stk = K + 1056`) -/
theorem cpostG_odd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {zp zc st xp xl yp yl mp n : Nat} {S s' : State}
    (h : ExpOdd.Post R b L K costF zp zc st xp xl yp yl mp n S s') :
    CPostG R b L (K + 1056) 112 zp zc st (natVal S.mem xp xl ^ natVal S.mem yp yl % natVal S.mem mp n)
      (ExpOdd.OCost costF n xl yl (stLen S.mem st)) S s' := by
  obtain ⟨p, l, c, q0, q1, q2, hv, hN, hlc, hc, L', b', hx, hb, hinv, hlive, hof, hsb, hF, hLF, hRS⟩ := h
  exact ⟨p, l, c, q0, q1, q2, L', b', ⟨hv, hN, hlc, ⟨hc.2, by have := (hlive hc.1).2.2.2; omega⟩, hlive, Or.inr hof⟩, ⟨hx, hb, hinv⟩, hsb, hF, hLF, hRS⟩

theorem odd_sub : ∀ x, ExpOdd.names.contains x = true → LibN.names.contains x = true := by
  have h : ExpOdd.names.Sublist LibN.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem odd_n11 : ExpOdd.names.contains Extracted.seg11.name = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the odd-modulus path from `expNNOdd`'s entry to expNN's return -/
theorem oddPath (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) {costF : Nat → Nat → Nat → Nat} (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW4 : nsD.contains Extracted.seg34.name = false) (hnsW2 : nsD.contains Extracted.seg35.name = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} (hKD : stkD ≤ K) {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hZ : ZM R b L g sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hm0 : s.mem.readLE mp 8 % 2 = 1) (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1))
    (hpc : S.pc = BitVec.ofNat 64 oddA) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (hA : DArgs S zq zcq st xp xl xc yp yl yc mp n mc) (h28 : S.regs 28 = s.regs 28)
    (h30 : S.regs 30 = BitVec.ofNat 64 1787680)
    (h29v : S.mem.readLE (sp + 1048) 8 = f29) (h30v : S.mem.readLE (sp + 1056) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, -, -, -, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, -, -⟩, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, -, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, -, hxN, hxl, hxp, hxc, -, -, -, -,
    -, -, hst0, hst48, hsok, hstw, -, harr, hc0, -, -, -, -, hrnd, -, -, -, hbud, -⟩ := hP'
  have hZ' := hZ
  obtain ⟨hF0, hLF0, hrg, hx1, hb1, hmk', hinv1, hZQ, hZA, hnz, hzq⟩ := hZ'
  have hs : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have hSs : S.sp.toNat = sp + 1056 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hg : (s.regs 28).toNat = g := by rw [hs28, BitVec.toNat_ofNat]; omega
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0 hF0 (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have hrdx : natVal S.mem xp xl = natVal s.mem xp xl := rd_held hxO.1 hLF0 hF0 hxO.2.1
  have hrdy : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hyO.1 hLF0 hF0 hyO.2.1
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  have hzc40 := hZQ.1
  have hE := ExpOdd.ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF hDiv hnsD hnsW4 hnsW2 b1 L1 K hKD (by omega)
    zq n zcq st xp xl xc yp yl yc mp n mc
  rw [show segAddr Extracted.program ExpOdd.fn = oddA by decide] at hE
  have hacc2 : S.mem.accessible (sp + 1048) 256 true = true := by
    rw [hF0.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hA
  refine callC impl hap odd_sub odd_n11 ret0 hret F hs hal hKs (by omega) hsp2 hLs hwrt hsok hstw hF0 hLF0 hx1
    hb1 hZA (Nat.le_refl _) h28 ?_ ?_ (Or.inr (Or.inr (Or.inl rfl))) hE hpc hSsp h30 ?_ ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
    (fun s' h => cpostG_odd h)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1) hacc2 h29v h30v hsl hEk
  · rw [hrdx, hrdy, hrdm]
  · rw [el]; unfold NCost; omega
  · simp only [ArgsFrom]
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, trivial⟩
  · rw [hSs, show sp + 1056 - 1056 = sp by omega, h28, hs28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact opre_at hP hZ hSsp (h28.trans hs28) hxl0 hyl0
  · rw [hrdm, val_mod2 hn]; exact hm0
  · rw [hrdm]; exact m_gt1 hn hmN hm1
  · rw [el]; omega
  · rw [el]; omega

end FvModexp.Arm64.ExpN
