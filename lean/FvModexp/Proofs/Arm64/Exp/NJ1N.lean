import FvModexp.Proofs.Arm64.Exp.NJ1
import FvModexp.Proofs.Arm64.Exp.NNilSK
import FvModexp.Proofs.Arm64.Exp.NNilQ

/-!
# `nat.expNN` (arm64), `stk == nil`: from `J1` to expNN's return (`fromJ1N`)

`NJ1.fromJ1` for the entry without a stack (`PreNil`, `ZKeep0`, `PostNil`): `NTriv.triv` (`postN_triv`; `NOne.one` →
`postN_oneA` / `postN_oneB`), else the stack branch `k2Nil` (`Get` / `newobject`, the computation, the deferred `Put`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fromJ1N (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (hget : PoolGetLive (LibN.program.link impl) getA 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract (LibN.program.link impl) noA 4096 R)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hX : NHyp.XFacts R L xp xl xc)
    (hev : NoEvenB s.mem mp n)
    (hz : ZKeep0 R L g sp K zp zl zc xp xl yp yl mp n zp' zl' zc' s.mem)
    (hna : NHyp.NoAlias zp' zc' xp xc)
    (S : State) (M : Memory) (hpc : S.pc = BitVec.ofNat 64 1786684) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h1 : S.regs 1 = BitVec.ofNat 64 zl') (h2 : S.regs 2 = BitVec.ofNat 64 zc')
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 mc)
    (h13 : S.regs 13 = BitVec.ofNat 64 slow)
    (h28 : S.regs 28 = s.regs 28) (hmem : S.mem = M)
    (hF : MemFrame s.mem M [(sp + 1048, sp + 1304), (sp + 1320, sp + 1408)]) (hrg : M.regions = s.mem.regions)
    (h29v : M.readLE (sp + 1048) 8 = f29) (h30v : M.readLE (sp + 1056) 8 = ret0)
    (hK' : ∀ s'' : State, s''.sp = BitVec.ofNat 64 (sp + 1312) → s''.regs 29 = BitVec.ofNat 64 f29 →
      s''.regs 18 = S.regs 18 → s''.regs 28 = S.regs 28 →
      PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, hd, hsv⟩, -, -, hro, hty, hslow,
    hn, hn128, -, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyc, hxO, hxa, hx48, -, hxl, hxp, hxc, hzp, hzlc,
    hzc, -, -, -, -, -, -, -, -, -, -, hbud0, -, -, hinv⟩ := hP'
  -- PATH MAX (expmc s44): keep only the max-free part of the budget in omega's context
  have hbud : 24 + makeCost 1 ≤ b := Nat.le_trans (by omega) hbud0
  clear hbud0
  have hs : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have hg : (s.regs 28).toNat = g := by rw [hs28, BitVec.toNat_ofNat]; omega
  have hFw : MemFrame s.mem M (wN sp K) := hF.mono fun a k ho => by
    simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  simp only [outside_cons] at hgo
  have hgw : Outside (g + 16) 8 [(sp + 1048, sp + 1304), (sp + 1320, sp + 1408)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have rdw : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1432) → M.readLE a k = s.mem.readLE a k := fun h =>
    hF.readLE _ _ (by unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega)
  have hm0M : M.readLE mp 8 = s.mem.readLE mp 8 := rdw (by have := hmO.2; unfold Apart at this ⊢; omega)
  have hx0M : 0 < xl → M.readLE xp 8 = s.mem.readLE xp 8 := fun h =>
    rdw (by have := (hxO h).2; unfold Apart at this ⊢; omega)
  have hy0M : 0 < yl → M.readLE yp 8 = s.mem.readLE yp 8 := fun h =>
    rdw (by have := (hyO h).2; unfold Apart at this ⊢; omega)
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hFw (fun r hr => Or.inr (out_rt_wN hwrt r hr)) hinv
  have hinvs : R.inv b L (s.regs 28).toNat (view R.rt L s.mem) := by rw [hg]; exact hinv
  have hzc' : zc' < 2 ^ 40 := by rcases hz with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩ <;> omega
  have hzp' : zp' < 2 ^ 64 := by rcases hz with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  have hS28 : S.regs 28 = BitVec.ofNat 64 g := h28.trans hs28
  refine triv impl ret0 hret F sp f29 xp xl yl mp n M hal (by omega) hsp2
    (by rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) (by omega) (by omega)
    (by omega) hxp (by omega)
    (fun h => by rw [hF.accessible]; exact Memory.accessible_mono _ hma (by omega) (by omega))
    (fun h => by rw [hF.accessible]; exact Memory.accessible_mono _ (hxa h) (by omega) (by omega))
    h29v h30v S hpc hsp h4 h5 h8 h10 h11 hmem ?F0 ?K1 ?K2
  case F0 =>
    intro hc s' e1 e2 e3 e4 e5 e6 e7 hF2 hrg2
    refine hK' s' e1 e2 e6 e7 (postN_triv hs hLs hwrt hinvs ?_ hzc hzp' ?_ ?_ (e3.trans h0) e4 (e5.trans h2))
    · rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨rfl, -, rfl⟩
      · refine Or.inl ⟨rfl, rfl, fun h => (hk h).2.2.2.2.1 h⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · refine val_triv hyN ?_
      rw [hm0M] at hc
      rcases hc with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · exact hFw.trans hF2 fun a k ho => ⟨ho, by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
  case K1 =>
    intro hm1 hyx T pc0 hpc0 e1 e2 e3 e4 e5 e6 e7
    rw [hm0M] at hm1
    have hM1 := m_gt1 hn hmN hm1
    have hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1 := by
      refine val_one hM1 ?_
      rcases hyx with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [← hx0M (by omega)]; exact h2⟩
    have hbl := blockSize_le_allocCost 8 true
    have e1c : makeCost 1 = allocCost 8 := rfl
    refine one impl R H.mkN ret0 hret F b L K g sp zp' zc' f29 pc0 M (S.regs 18) hpc0 hal hK4 hKs hsp2
      (by rw [hF.accessible]; exact hacc) hg1 (by rw [hF.accessible]; exact hg2)
      (by rw [hF.readLE _ _ hgw]; exact hg3) hout (by unfold Apart; omega) hgo.2 hLs
      (dataLoaded_frame hd hrg hro.1 (hFw.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) (fun r hr _ => by
        simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)))
      hro.1 hty (by omega) hzp' ?_ (fun _ => ⟨hsv.1 _ _ _ (by omega), by omega⟩) hinvM h29v h30v T e1 (e2.trans hsp)
      (e3.trans h0) (e4.trans h2) e5 (e6.trans hS28) e7 ?FA ?FB
    · intro hc
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨-, hw⟩, ha, h48, -⟩ := hk hc
        exact ⟨by rw [hF.accessible]; exact Memory.accessible_mono _ ha (by omega) (by omega), by omega,
          Apart.mono hw (by omega) (Nat.le_refl _)⟩
      · omega
    case FA =>
      intro hc s' f1 f2 f3 f4 f5 f6 f7 hF2 hv1 hrg2
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨hH, -⟩, -, -, -, hzL, -⟩ := hk hc
        refine hK' s' f1 f2 f6 (f7.trans hS28.symm) (postN_oneA hs hLs hwrt hinvs hc hzc hH hzL hv ?_
          hv1 f3 f4 f5)
        exact hFw.trans hF2 fun a k ho => ⟨by rw [List.cons_append, outside_cons] at ho; exact ho.2,
          by simp only [wN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      · omega
    case FB =>
      intro hc s' p r m hLF hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv' f1 f2 f3 f4 f5 f6 f7 hF2 hv1 hrg2
      exact hK' s' f1 f2 f6 (f7.trans hS28.symm) (postN_oneB hs hK4 hLs hwrt hv hFw hLF hMF hAp hIn hp48
        haccp hp8 hr8 hr (by rw [hg]; exact hinv') hF2 hv1 f3 f4 f5)
  case K2 =>
    intro hm1 hy0 hx0 _ T tpc tsp t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t18 t28 tm
    rw [hm0M] at hm1
    exact k2Nil impl hap R hget hno hput hRem hnsR hn11R hKR H ret0 hret F hP hX hz hna hm1 hev hx0 hy0 M hF hrg h29v h30v T
      tpc (tsp.trans hsp) (t0.trans h0) (t1.trans h1) (t2.trans h2) (t3.trans h3) (t4.trans h4) (t5.trans h5)
      (t6.trans h6) (t7.trans h7) (t8.trans h8) (t9.trans h9) (t10.trans h10) (t11.trans h11) (t12.trans h12)
      (t13.trans h13) (t28.trans h28) tm
      fun s'' a1 a2 a3 a4 hq => hK' s'' a1 a2 (a3.trans t18) (a4.trans t28) hq

end FvModexp.Arm64.ExpN
