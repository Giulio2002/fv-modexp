import FvModexp.Proofs.Arm64.Exp.NNilS

/-!
# `nat.expNN` (arm64), `stk == nil`: `Get` returned nil (`k2N`)

From `Get`'s return (`X0 = X1 = 0`): `getN` → `newobject(type:big.stack)` (`noCallN`) → `joinN` (the defer record, the
reloads, the join) then `contR` (`y == 1`) or `contD` (`J5`), with the new stack `NewStk` from `newStk_N` (budget `b - 24`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem k2N (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hno : NewobjectLiveContract (LibN.program.link impl) noA 4096 R)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {ns : List String} {stk : Nat} (hRem : NHyp.RemHyp impl R ns stk 112 needR costR)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hn11 : ns.contains Extracted.seg11.name = false)
    (hstk : stk ≤ K + 1056)
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow f29 zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow s)
    (hz : ZKeep0 R L g sp K zp zl zc xp xl yp yl mp n zp' zl' zc' s.mem)
    (hna : NHyp.NoAlias zp' zc' xp xc)
    (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hev : NoEvenB s.mem mp n) (hx0 : xl ≠ 0) (hy0 : yl ≠ 0)
    (Mg : Memory) (hFg : MemFrame s.mem Mg (R.rt ++ wN sp K) ∧ LiveFrame s.mem Mg L [])
    (hrgg : Mg.regions = s.mem.regions)
    (g208 : Mg.readLE (sp + 1056 + 208) 8 = zp') (g152 : Mg.readLE (sp + 1056 + 152) 8 = zl')
    (g168 : Mg.readLE (sp + 1056 + 168) 8 = zc')
    (g296 : Mg.readLE (sp + 1056 + 296) 8 = xp) (g304 : Mg.readLE (sp + 1056 + 304) 8 = xl)
    (g312 : Mg.readLE (sp + 1056 + 312) 8 = xc) (g320 : Mg.readLE (sp + 1056 + 320) 8 = yp)
    (g328 : Mg.readLE (sp + 1056 + 328) 8 = yl) (g336 : Mg.readLE (sp + 1056 + 336) 8 = yc)
    (g344 : Mg.readLE (sp + 1056 + 344) 8 = mp) (g352 : Mg.readLE (sp + 1056 + 352) 8 = n)
    (g360 : Mg.readLE (sp + 1056 + 360) 8 = mc) (g368 : Mg.readLE (sp + 1056 + 368) 1 = 0)
    (g1048 : Mg.readLE (sp + 1048) 8 = f29) (g1056 : Mg.readLE (sp + 1056) 8 = ret0)
    (r18 r28 : BitVec 64) (hr28 : r28 = s.regs 28)
    (hK' : ∀ s'' : State, s''.sp = BitVec.ofNat 64 (sp + 1312) → s''.regs 29 = BitVec.ofNat 64 f29 →
      s''.regs 18 = r18 → s''.regs 28 = r28 →
      PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s'' → F s'')
    (m : Memory) (hMFm : MemFrame Mg m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)]))
    (hLFm : LiveFrame Mg m L []) (hrgm : m.regions = Mg.regions) (hinvm : R.inv b L g (view R.rt L m))
    (S3 : State) (p3 : S3.pc = BitVec.ofNat 64 getR) (sp3 : S3.sp = BitVec.ofNat 64 (sp + 1056))
    (x0 : S3.regs 0 = 0#64) (x1 : S3.regs 1 = 0#64) (x18 : S3.regs 18 = r18)
    (x28 : S3.regs 28 = r28) (hm3 : S3.mem = m) :
    Reaches ((LibN.program.link impl).withExit ret0) S3 (IsReturn F) := by
  obtain ⟨⟨-, hs28, hg1, hg2, hg3, hgo, hal, hK4, hKs, hsp2, hwacc, hwrt, hLs, hd, hsv⟩, -, -, ⟨hro, hz0⟩, -, -,
    -, -, -, -, -, -, -, -, hyO, hya, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbud,
    -⟩ := id hP
  replace hyO := hyO (by omega); replace hya := hya (by omega)
  have hwout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  have hgrt : Outside (g + 16) 8 R.rt := hgo.2
  have hgw : Apart (g + 16) 8 (sp - K) (K + 1432) := by
    have := hgo.1; unfold Apart; omega
  have hgwN : Outside (g + 16) 8 (R.rt ++ wN sp K) := by
    have := hgo.1; rw [outside_append]; exact ⟨hgrt, by simp only [wN, outside_cons, outside_nil, and_true]; omega⟩
  clear hgo
  have hFm := chain hFg hMFm hLFm (sub_cw hK4 hKs)
  have rdm := rd_cw hK4 hKs hwout hMFm
  have hyW : yp + 8 * yl ≤ sp - K ∨ sp - K + (K + 1432) ≤ yp := hyO.2
  have hyo : yp + 8 ≤ sp + 1182 ∨ sp + 1425 ≤ yp := by omega
  clear hyW
  have hdm : Extracted.program.DataLoaded m := dataLoaded_frame hd (by rw [hrgm, hrgg]) hro hFm.1 (fun r hr _ => by
    simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hwacc (by omega) (by omega))
  have hacm : m.accessible (sp + 1048) 384 true = true := by
    rw [hFm.1.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)
  have hb24 : 24 ≤ b := by omega
  clear hbud
  refine getN impl ret0 hret _ sp m hal (by omega) hsp2 hacm S3 p3 sp3 x0 x1 hm3 ?_
  intro S5 p5 sp5 y0 y18 y28 y29 y30 hm5
  refine noCallN impl R hno ret0 hret _ b L K g sp m hal hK4 hKs hsp2
    (by rw [hFm.1.accessible]; exact hwacc) hg1 (by rw [hFm.1.accessible]; exact hg2)
    (by rw [hFm.1.readLE _ _ hgwN]; exact hg3) hwout hgw hgrt hLs hdm hsv hinvm hb24 S5 p5 (sp5.trans sp3) y0
    (y28.trans (x28.trans (hr28.trans hs28))) y30 hm5 ?_
  intro S6 m2 p p6 sp6 z0 hp64 z18 z28 z29 hm6 hNN
  have hFm2 := chain hFm hNN.mf hNN.lf (sub_cw hK4 hKs)
  have rdm2 : ∀ a k, (sp + 1048 ≤ a ∧ a + k ≤ sp + 1064) ∨ (sp + 1072 ≤ a ∧ a + k ≤ sp + 1432) →
      m2.readLE a k = Mg.readLE a k := fun a k ha => (rd_cw hK4 hKs hwout hNN.mf a k ha).trans (rdm a k ha)
  have hyM : m2.readLE yp 8 = s.mem.readLE yp 8 := by
    have hyW : yp + 8 * yl ≤ sp - K ∨ sp - K + (K + 1432) ≤ yp := hyO.2
    exact rd_mk (held_sub hyO.1 (Nat.le_refl _) (by omega)) hFm2.2 hFm2.1
      (by simp only [wN, outside_cons, outside_nil, and_true]; omega)
  refine joinN impl ret0 hret _ sp p zp' zl' zc' xp xl xc yp yl yc mp n mc 0 m2 hal (by omega) hsp2
    (by rw [hFm2.1.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)) hp64
    (by rw [rdm2 _ _ (by omega)]; exact g208) (by rw [rdm2 _ _ (by omega)]; exact g152)
    (by rw [rdm2 _ _ (by omega)]; exact g168) (by rw [rdm2 _ _ (by omega)]; exact g296)
    (by rw [rdm2 _ _ (by omega)]; exact g304) (by rw [rdm2 _ _ (by omega)]; exact g312)
    (by rw [rdm2 _ _ (by omega)]; exact g320) (by rw [rdm2 _ _ (by omega)]; exact g328)
    (by rw [rdm2 _ _ (by omega)]; exact g336) (by rw [rdm2 _ _ (by omega)]; exact g344)
    (by rw [rdm2 _ _ (by omega)]; exact g352) (by rw [rdm2 _ _ (by omega)]; exact g360)
    (by rw [rdm2 _ _ (by omega)]; exact g368)
    (by rw [hFm2.1.accessible]; exact Memory.accessible_mono _ hya (by omega) (by omega)) hyo hy0
    S6 p6 (sp6.trans (sp5.trans sp3)) z0 hm6 ?_ ?_
  · intro hy1 hyv S4 M4 p4 sp4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a18 a28 a30 hm4 hF4 hrg4 f1182 _ f1272 f1280 f1296
    have hN := newStk_N hNN hz0 hb24 hF4 (slots_rt hKs hwout)
    have hF5 := chainW hFm2 hF4 hLs (slots_win hKs) (sub_slots hKs)
    exact contR impl hap R hput hRem hns hn11 ret0 hret F hP hstk hN hF5.1 hF5.2 (by rw [hrg4, hNN.rg, hrgm, hrgg])
      f1182 f1296 f1272 f1280 hz hna ⟨hy1, by rw [← hyM]; exact hyv⟩ hx0 S4 p4 (sp4.trans (sp6.trans (sp5.trans sp3)))
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (a28.trans (z28.trans (y28.trans (x28.trans hr28)))) a30 hm4
      (by rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g1048)
      (by rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g1056)
      fun s'' e1 e2 e3 e4 hq => hK' s'' e1 e2 (e3.trans (a18.trans (z18.trans (y18.trans x18))))
        (e4.trans (a28.trans (z28.trans (y28.trans x28)))) hq
  · intro hny S4 M4 p4 sp4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a18 a28 hm4 hF4 hrg4 f1182 _ f1272 f1280
      f1296
    have hN := newStk_N hNN hz0 hb24 hF4 (slots_rt hKs hwout)
    have hF5 := chainW hFm2 hF4 hLs (slots_win hKs) (sub_slots hKs)
    rw [hyM] at hny
    have hspl : SpillsB M4 sp xp xl xc yp yl yc mp n mc := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g296
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g304
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g312
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g320
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g328
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g336
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g344
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g352
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g360
      · rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g368
    exact contD impl hap R hput H ret0 hret F hP hN hF5.1 hF5.2 (by rw [hrg4, hNN.rg, hrgm, hrgg])
      f1182 f1296 f1272 f1280 hz hx0 hy0 hny hm1 hev S4 p4 (sp4.trans (sp6.trans (sp5.trans sp3))) a0 a2 a3 a4 a5 a6
      a7 a8 a9 a10 a11 a12 a13 (a28.trans (z28.trans (y28.trans (x28.trans hr28)))) hm4 hspl
      (by rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g1048)
      (by rw [rd_sl hF4 _ _ (by omega), rdm2 _ _ (by omega)]; exact g1056)
      fun s'' e1 e2 e3 e4 hq => hK' s'' e1 e2 (e3.trans (a18.trans (z18.trans (y18.trans x18))))
        (e4.trans (a28.trans (z28.trans (y28.trans x28)))) hq

end FvModexp.Arm64.ExpN
