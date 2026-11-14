import FvModexp.Proofs.Amd64.Exp.NNilJ
import FvModexp.Proofs.Amd64.Exp.NNewE

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the two `Get` outcomes (agent expmc s75; twin of `Arm64.ExpN` NNilST/NNilSN)

At `Get`'s return (`getR`, `RSP = t - 0x108`, memory `m`):
* `nilPool`: a pooled `*stack` `d` (`StkSh`, fresh ranges `rs`): `getTE` → `nilJ` (`NewStk` by `DivNil.newStk_T`).
* `nilNew`: the pool was empty: `getNE` → `newobject(type:big.stack)` (`noCallE`, descriptor facts from rodata) →
  `noRetE` → `nilJ` (`NewStk` by `newStk_NM`, budget `b - 24`).
* `cenv_wN`: `CEnv` across a frame `R.rt ++ wN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

theorem cenv_wN {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {M M' : Janus.Arm64.Memory}
    (h : CallW.CEnv R L g fs sp K 0x510 M) (hF : MemFrame M M' (R.rt ++ wN sp K)) (hrg : M'.regions = M.regions) :
    CallW.CEnv R L g fs sp K 0x510 M' := by
  have h' := h
  obtain ⟨hal, hKs, hsp2, hacc, -, -, -, -, hgw, -, -, -, -, -, -, -, -, -, f6⟩ := h'
  exact CallW.CEnv.frame h hF hrg (fun r hr _ => by
      simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    (by unfold Apart at hgw; simp only [wN, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [wN, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `Get` returned a pooled stack -/
theorem nilPool (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow bp zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hX : NHyp.XFacts R L xp xl xc)
    (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem) (hna : NHyp.NoAlias zp' zc' xp xc)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hEv : EvH impl R K needS costS xl yl n)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = s.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'')
    (m : Janus.Arm64.Memory) (hMF : MemFrame s.mem m (R.rt ++ wN sp K) ∧ LiveFrame s.mem m L [])
    (hrg : m.regions = s.mem.regions)
    (hA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → m.readLE a k = s.mem.readLE a k)
    (hsp : NilSp m (sp + 0x498) zp' zl' zc' yc xp xl xc 0 n yp mp yl mc)
    (hbp : m.readLE (sp + 0x490) 8 = bp) (hrv : m.readLE (sp + 0x498) 8 = ret0)
    {d : Nat} {rs : List (Nat × Nat)} (hd : d < 2 ^ 64) (hSh : StkSh m d rs) (hfr : FreshFrom rs L)
    (hin : ∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) (hinv : R.inv b (L ++ rs) g (view R.rt (L ++ rs) m))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 getR) (hS4 : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : S.regs 0 = BitVec.ofNat 64 Free.stkT) (h3 : S.regs 3 = BitVec.ofNat 64 d) (hmem : S.mem = m)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = 0) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  obtain ⟨⟨-, -, -, -, -, -, -, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hyO, hya, -⟩ := id hP
  obtain ⟨hal, hKs, hsp2, hwacc, -, -, -, hwout, -⟩ := hce
  have hN := newStk_T (ws := []) hSh hfr hin hinv (MemFrame.refl m []) (fun r hr => by simp at hr)
  have hyO' := hyO (by omega)
  have hya' := hya (by omega)
  refine getTE impl ret0 hret (IsReturn F) (sp + 0x498) d zp' zl' zc' yc xp xl xc 0 n yp mp yl mc m (by omega)
    (by omega) (by rw [hMF.1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)) hd
    hN.2.2.1 hsp hyl0 (by rw [hMF.1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hya' (by omega) (by omega))
    (by have := hyO'.2; unfold Apart at this; omega) S hpc (hS4.trans (congrArg _ (by omega))) h0 h3 hmem
    (nilJ impl hap R hput H hRem hnsR hnfR hKR ret0 hret F hP hX hz hna hxl0 hyl0 hm1 hEv hN hMF.1 hMF.2 hrg hA hsp
      hbp hrv S hS4 h14 hfs hdf hx15 hK')

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `Get` returned nil: a new `*stack` -/
theorem nilNew (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract64 (LibNE.program.link impl) (cA "runtime.newobject") 4096 R)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow bp zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hX : NHyp.XFacts R L xp xl xc)
    (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem) (hna : NHyp.NoAlias zp' zc' xp xc)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hEv : EvH impl R K needS costS xl yl n)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = s.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'')
    (m : Janus.Arm64.Memory) (hMF : MemFrame s.mem m (R.rt ++ wN sp K) ∧ LiveFrame s.mem m L [])
    (hrg : m.regions = s.mem.regions)
    (hA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → m.readLE a k = s.mem.readLE a k)
    (hsp : NilSp m (sp + 0x498) zp' zl' zc' yc xp xl xc 0 n yp mp yl mc)
    (hbp : m.readLE (sp + 0x490) 8 = bp) (hrv : m.readLE (sp + 0x498) 8 = ret0)
    (hinv : R.inv b L g (view R.rt L m))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 getR) (hS4 : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : S.regs 0 = 0#64) (h3 : S.regs 3 = 0#64) (hmem : S.mem = m)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = 0) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  obtain ⟨⟨-, hs14, -, -, -, hK1, -, hce, hsv⟩, -, hPG, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hyO, hya, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbud, -⟩ := id hP
  have hce' := hce
  obtain ⟨hal, hKs, hsp2, hwacc, hg1, -, -, hwout, hgw, -, hLs, -⟩ := hce'
  have hyO' := hyO (by omega)
  have hya' := hya (by omega)
  have ht : sp + 0x498 - 0x110 = sp + 0x388 := by omega
  refine getNE impl ret0 hret (IsReturn F) (sp + 0x498) m (by omega) (by omega)
    (by rw [ht, hMF.1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega))
    S hpc (hS4.trans (congrArg _ (by omega))) h0 h3 hmem ?_
  intro X xpc x4 x0 x5 x14 xfs xdf xx xm
  rw [ht] at x4 xm
  generalize hMw : m.writeLE (sp + 0x388) 8 noR = Mw at xm
  have hFw : MemFrame m Mw [(sp + 0x388, sp + 0x390)] := by
    rw [← hMw]
    exact ⟨fun a k ho => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by
      simp only [outside_cons, outside_nil, and_true] at ho; omega), fun a k w => by
      simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
  have hrgw : Mw.regions = m.regions := by rw [← hMw]; simp only [Janus.Arm64.Memory.regions_writeLE]
  have hMw' := chainW hMF hFw hLs (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; omega)
    fun a k ho => by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hcew := cenv_wN hce hMw'.1 (hrgw.trans hrg)
  obtain ⟨-, -, -, hwacc', hg1', hg2', hg3', -, -, -, -, hdl, -⟩ := hcew
  have hinvw : R.inv b L g (view R.rt L Mw) := Expmc.inv_frame hFw (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inr (hwout.of_sub (by simp only; omega)
      (by simp only; omega))) hinv
  obtain ⟨ta, t1, t2⟩ := stkTy_data hdl
  have hAd : Apart 7357344 16 (sp - K) (K + 0x510) := apart_of_data hdl 4 (by decide) (by decide) hwacc'
  have hg14 : X.regs 14 = BitVec.ofNat 64 g := x14.trans (h14.trans hs14)
  refine noCallE impl R hno ret0 hret (IsReturn F) b L K g sp Mw hal hK1 hKs hsp2 hwacc' hg1' hg2' hg3' hwout hgw
    hLs hsv hinvw (by omega) ta t1 t2 hAd X xpc x4 hg14 x0 xm
    (by rw [← hMw]; exact (rd_wr_eq rfl).trans (by decide)) ?_
  intro S2 p p0 p4 p5 p14 pfs px pdf pr0 hp hNN
  have hN := newStk_NM (ws := []) hNN hPG.1 (by omega) (MemFrame.refl _ []) (fun r hr => by simp at hr)
  have hM2 := chainR hMw' hNN.mf hNN.lf fun a k ho => by
    simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd2 : ∀ a k, sp + 0x398 ≤ a → a + k ≤ sp + 0x510 → S2.mem.readLE a k = m.readLE a k := fun a k h1 h2 => by
    rw [hNN.mf.readLE a k (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwout.of_sub (by omega) (by omega), by omega, by omega⟩),
      hFw.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩ := hsp
  have hsp2 : NilSp S2.mem (sp + 0x498) zp' zl' zc' yc xp xl xc 0 n yp mp yl mc :=
    ⟨by rw [rd2 _ _ (by omega) (by omega)]; exact r1, by rw [rd2 _ _ (by omega) (by omega)]; exact r2,
      by rw [rd2 _ _ (by omega) (by omega)]; exact r3, by rw [rd2 _ _ (by omega) (by omega)]; exact r4,
      by rw [rd2 _ _ (by omega) (by omega)]; exact r5, by rw [rd2 _ _ (by omega) (by omega)]; exact r6,
      by rw [rd2 _ _ (by omega) (by omega)]; exact r7, by rw [rd2 _ _ (by omega) (by omega)]; exact r8,
      by rw [rd2 _ _ (by omega) (by omega)]; exact r9, by rw [rd2 _ _ (by omega) (by omega)]; exact r10,
      by rw [rd2 _ _ (by omega) (by omega)]; exact r11, by rw [rd2 _ _ (by omega) (by omega)]; exact r12,
      by rw [rd2 _ _ (by omega) (by omega)]; exact r13⟩
  have hacS : ∀ a k w, S2.mem.accessible a k w = s.mem.accessible a k w := fun a k w => hM2.1.accessible a k w
  refine noRetE impl ret0 hret (IsReturn F) (sp + 0x498) p zp' zl' zc' yc xp xl xc 0 n yp mp yl mc S2.mem (by omega)
    (by omega) (by rw [hacS]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)) hp hN.2.2.1
    hsp2 hyl0 (by rw [hacS]; exact Janus.Arm64.Memory.accessible_mono _ hya' (by omega) (by omega))
    (by have := hyO'.2; unfold Apart at this; omega) S2 p0 (p4.trans (congrArg _ (by omega))) pr0 rfl
    (nilJ impl hap R hput H hRem hnsR hnfR hKR ret0 hret F hP hX hz hna hxl0 hyl0 hm1 hEv hN hM2.1 hM2.2
      (hNN.rg.trans (hrgw.trans hrg)) (fun a k h1 h2 => (rd2 a k (by omega) (by omega)).trans (hA a k h1 h2)) hsp2
      (by rw [rd2 _ _ (by omega) (by omega)]; exact hbp) (by rw [rd2 _ _ (by omega) (by omega)]; exact hrv)
      S2 p4 (p14.trans (x14.trans h14)) (pfs.trans (xfs.trans hfs)) (pdf.trans (xdf.trans hdf))
      (px.trans (xx.trans hx15)) hK')

end FvModexp.Amd64.ExpN
