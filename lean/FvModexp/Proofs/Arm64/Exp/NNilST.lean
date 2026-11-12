import FvModexp.Proofs.Arm64.Exp.NNilS

/-!
# `nat.expNN` (arm64), `stk == nil`: `Get` returned a pooled stack (`k2T`)

From `Get`'s return (`X0 = type:big.stack`, `X1 = d`, `StkSh m d rs`): `getT` (the defer record, the reloads, the join)
then `contR` (`y == 1`) or `contD` (`J5`), with the new stack `NewStk` from `newStk_T`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem k2T
    (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (m : Memory) (d : Nat) (rs : List (Nat × Nat))
    (hMFm : MemFrame Mg m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)]))
    (hLFm : LiveFrame Mg m L []) (hrgm : m.regions = Mg.regions)
    (hSh : StkSh m d rs) (hfr : FreshFrom rs L) (hin : ∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt)
    (hinv3 : R.inv b (L ++ rs) g (view R.rt (L ++ rs) m))
    (S3 : State) (p3 : S3.pc = BitVec.ofNat 64 getR) (sp3 : S3.sp = BitVec.ofNat 64 (sp + 1056))
    (x0 : S3.regs 0 = BitVec.ofNat 64 Free.stkT) (x1 : S3.regs 1 = BitVec.ofNat 64 d) (x18 : S3.regs 18 = r18)
    (x28 : S3.regs 28 = r28) (hm3 : S3.mem = m) :
    Reaches ((LibN.program.link impl).withExit ret0) S3 (IsReturn F) := by
  obtain ⟨⟨-, -, -, -, -, -, hal, hK4, hKs, hsp2, hwacc, hwrt, hLs, -, -⟩, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hyO, hya, -⟩ := id hP
  have hwout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  have hFm := chain hFg hMFm hLFm (sub_cw hK4 hKs)
  have rdm := rd_cw hK4 hKs hwout hMFm
  have hyW : yp + 8 * yl ≤ sp - K ∨ sp - K + (K + 1432) ≤ yp := hyO.2
  have hyo : yp + 8 ≤ sp + 1182 ∨ sp + 1425 ≤ yp := by omega
  have hyM : m.readLE yp 8 = s.mem.readLE yp 8 :=
    rd_mk (held_sub hyO.1 (Nat.le_refl _) (by omega)) hFm.2 hFm.1
      (by simp only [wN, outside_cons, outside_nil, and_true]; omega)
  clear hyW
  obtain ⟨hd0, -, hd48, -⟩ := hSh.ok
  refine getT impl ret0 hret _ sp d zp' zl' zc' xp xl xc yp yl yc mp n mc 0 m hal (by omega) hsp2
    (by rw [hFm.1.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)) (by omega) hd0
    (by rw [rdm _ _ (by omega)]; exact g208) (by rw [rdm _ _ (by omega)]; exact g152)
    (by rw [rdm _ _ (by omega)]; exact g168) (by rw [rdm _ _ (by omega)]; exact g296)
    (by rw [rdm _ _ (by omega)]; exact g304) (by rw [rdm _ _ (by omega)]; exact g312)
    (by rw [rdm _ _ (by omega)]; exact g320) (by rw [rdm _ _ (by omega)]; exact g328)
    (by rw [rdm _ _ (by omega)]; exact g336) (by rw [rdm _ _ (by omega)]; exact g344)
    (by rw [rdm _ _ (by omega)]; exact g352) (by rw [rdm _ _ (by omega)]; exact g360)
    (by rw [rdm _ _ (by omega)]; exact g368)
    (by rw [hFm.1.accessible]; exact Memory.accessible_mono _ hya (by omega) (by omega)) hyo hy0
    S3 p3 sp3 x0 x1 hm3 ?_ ?_
  · intro hy1 hyv S4 M4 p4 sp4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a18 a28 a30 hm4 hF4 hrg4 f1182 _ f1272 f1280 f1296
    have hN := newStk_T hSh hfr hin hinv3 hF4 (slots_rt hKs hwout)
    have hF5 := chainW hFm hF4 hLs (slots_win hKs) (sub_slots hKs)
    exact contR impl hap R hput hRem hns hn11 ret0 hret F hP hstk hN hF5.1 hF5.2 (by rw [hrg4, hrgm, hrgg])
      f1182 f1296 f1272 f1280 hz ⟨hy1, by rw [← hyM]; exact hyv⟩ S4 p4 (sp4.trans sp3) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
      (a28.trans (x28.trans hr28)) a30 hm4
      (by rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g1048)
      (by rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g1056)
      fun s'' e1 e2 e3 e4 hq => hK' s'' e1 e2 (e3.trans (a18.trans x18)) (e4.trans (a28.trans x28)) hq
  · intro hny S4 M4 p4 sp4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a18 a28 hm4 hF4 hrg4 f1182 _ f1272 f1280
      f1296
    have hN := newStk_T hSh hfr hin hinv3 hF4 (slots_rt hKs hwout)
    have hF5 := chainW hFm hF4 hLs (slots_win hKs) (sub_slots hKs)
    rw [hyM] at hny
    have hspl : SpillsB M4 sp xp xl xc yp yl yc mp n mc := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g296
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g304
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g312
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g320
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g328
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g336
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g344
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g352
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g360
      · rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g368
    exact contD impl hap R hput H ret0 hret F hP hN hF5.1 hF5.2 (by rw [hrg4, hrgm, hrgg])
      f1182 f1296 f1272 f1280 hz hx0 hy0 hny hm1 hev S4 p4 (sp4.trans sp3) a0 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
      (a28.trans (x28.trans hr28)) hm4 hspl
      (by rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g1048)
      (by rw [rd_sl hF4 _ _ (by omega), rdm _ _ (by omega)]; exact g1056)
      fun s'' e1 e2 e3 e4 hq => hK' s'' e1 e2 (e3.trans (a18.trans x18)) (e4.trans (a28.trans x28)) hq

end FvModexp.Arm64.ExpN
