import FvModexp.Proofs.Arm64.Exp.NMid
import FvModexp.Proofs.Arm64.Exp.NEvP
import FvModexp.Proofs.Arm64.Exp.NMkE
import FvModexp.Proofs.Arm64.Exp.NDispE

/-!
# `nat.expNN` (arm64): from `J5` to expNN's return, every modulus (`fromJ5E`, on `LibNE`)

`NMid.fromJ5` without the `noEven` restriction: the slow / odd / power-of-two paths (on `LibN`, lifted by `liftNE`)
and, for an even modulus that is not a power of two, the `expNNEven` path `evPath` (infra's `ExpEven.EvenSum`; its
need/cost bounded by the slow slot's, `hnE`/`hcE`). The make and the dispatch run on `LibNE` (`mkE`, `dispE`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fromJ5E (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {stkE : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hEv : ExpEven.EvenSum impl R stkE 112 needE costE) (hstkE : stkE ≤ K + 1056)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 zp' zc' : Nat}
    {s : State}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hX : NHyp.XFacts R L xp xl xc)
    (hz : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g sp K st zp zc xp xl yp yl mp n s.mem)) ∨ (zp' = 0 ∧ zc' = 0))
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1))
    (hnE : needE xl yl n ≤ needS xl yl n) (hcE : ∀ l, costE l xl yl n ≤ costS l xl yl n)
    (S : State) (M : Memory) (hpc : S.pc = BitVec.ofNat 64 1787348) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h2 : S.regs 2 = BitVec.ofNat 64 zc')
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 mc) (h13 : S.regs 13 = 0#64)
    (h28 : S.regs 28 = s.regs 28) (hmem : S.mem = M)
    (hF : MemFrame s.mem M (wN sp K)) (hrg : M.regions = s.mem.regions)
    (hsp : SpillsB M sp xp xl xc yp yl yc mp n mc)
    (h29v : M.readLE (sp + 1048) 8 = f29) (h30v : M.readLE (sp + 1056) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq M M0 sp)
    (hE : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, hd, hsv⟩, -, -, hro, hty, -,
    hn, hn128, -, hmc, hmO, hma, hm48, -, hyO, hya, hy48, -, hyl, hyc, -, -, -, -, hxl, hxp, hxc, hzp, -, hzc, -,
    -, -, -, hst48, -, -, -, -, -, -, -, -, -, -, -, -, -, hbud, hinv⟩ := hP'
  have hg : (s.regs 28).toNat = g := by rw [hs28, BitVec.toNat_ofNat]; omega
  have hLF : LiveFrame s.mem M L [] := LiveFrame.of_win hF (liveSep_wN hLs)
  have hF' : MemFrame s.mem M (R.rt ++ wN sp K) := hF.mono fun a k ho => by rw [outside_append] at ho; exact ho.2
  have hout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  simp only [outside_cons] at hgo
  have hgw : Outside (g + 16) 8 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; omega
  have hrd : ∀ {a k : Nat}, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - K) (K + 1432) →
      M.readLE a k = s.mem.readLE a k := fun hH hw => rd_held hH hLF hF' hw
  have hm0M : M.readLE mp 8 = s.mem.readLE mp 8 :=
    hrd (a := mp) (k := 8) (held_sub hmO.1 (by omega) (by omega)) (by have := hmO.2.1; unfold Apart at this ⊢; omega)
  have hy0M : M.readLE yp 8 = s.mem.readLE yp 8 :=
    hrd (a := yp) (k := 8) (held_sub hyO.1 (by omega) (by omega)) (by have := hyO.2.1; unfold Apart at this ⊢; omega)
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hF (fun r hr => Or.inr (out_rt_wN hwrt r hr)) hinv
  have hzc' : zc' < 2 ^ 40 := by rcases hz with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> omega
  have hzp' : zp' < 2 ^ 64 := by rcases hz with ⟨rfl, -, -⟩ | ⟨rfl, -⟩ <;> omega
  have hmc1 : makeCap n ≤ n + 4 := by unfold makeCap; split <;> omega
  have hbl : blockSize (8 * makeCap n) true ≤ makeCost n := blockSize_le_allocCost _ _
  -- the three dispatch targets, from a dispatch start point with context `ZM`
  have tgt : ∀ (D : State) (M1 : Memory) (L1 : List (Nat × Nat)) (b1 zq zcq mk : Nat),
      ZM R b L g sp K zp zc st xp xl yp yl mp n s.mem M1 L1 b1 zq zcq mk →
      M1.readLE (sp + 1048) 8 = f29 → M1.readLE (sp + 1056) 8 = ret0 → SlotEq M1 M0 sp →
      M1.accessible (sp + 1048) 384 true = true →
      D.sp = BitVec.ofNat 64 (sp + 1056) → DStart D sp zq zcq st xp xl xc yp yl yc mp n mc → D.mem = M1 →
      D.regs 18 = S.regs 18 → D.regs 28 = S.regs 28 →
      Reaches ((LibNE.program.link impl).withExit ret0) D (IsReturn F) := by
    intro D M1 L1 b1 zq zcq mk hZ f1 f2 f3 hacc1 hDsp hDS hDm hD18 hD28
    have hZ' := hZ
    obtain ⟨hF1, hLF1, -, -, -, -, -, hZQ, -, -, hzq⟩ := hZ'
    have hrd1 : ∀ {a k : Nat}, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - K) (K + 1432) →
        M1.readLE a k = s.mem.readLE a k := fun hH hw => rd_held hH hLF1 hF1 hw
    have hm01 : M1.readLE mp 8 = s.mem.readLE mp 8 :=
      hrd1 (a := mp) (k := 8) (held_sub hmO.1 (by omega) (by omega)) (by have := hmO.2.1; unfold Apart at this ⊢; omega)
    have hy01 : M1.readLE yp 8 = s.mem.readLE yp 8 :=
      hrd1 (a := yp) (k := 8) (held_sub hyO.1 (by omega) (by omega)) (by have := hyO.2.1; unfold Apart at this ⊢; omega)
    refine dispE impl ret0 hret _ sp zq zcq st xp xl xc yp yl yc mp n mc M1 hzq (by have := hZQ.1; omega) (by omega)
      hxp (by omega) hxc (by omega) (by omega) hyc (by omega) (by omega) (by omega)
      (by rw [hF1.accessible]; exact Memory.accessible_mono _ hya (by omega) (by omega))
      (by rw [hF1.accessible]; exact Memory.accessible_mono _ hma (by omega) (by omega))
      hal (by omega) hsp2 hacc1 D hDsp hDS hDm ?_ ?_ ?_
    · intro _ _ S' e1 e2 e3 e4 e5 e6 e7
      rw [← e7] at hZ f1 f2 f3
      exact liftNE impl hap <| slowPath impl hap R H.slow H.hnsS H.hn11S ret0 (retAddr_down hret) F hP hX H.hKS hZ hxl0 hyl0 hy1 e1 (e2.trans hDsp) e3
        ((e5.trans hD28).trans h28) e6 f1 f2 f3 (by rw [e4, hD18, e5, hD28]; exact hE)
    · intro _ hodd S' e1 e2 e3 e4 e5 e6 e7
      rw [← e7] at hZ f1 f2 f3
      exact liftNE impl hap <| oddPath impl hap R H.clr H.mv H.mkO H.gr H.wb nsD stkD H.div H.hnsD H.hnsW4 H.hnsW2 ret0 (retAddr_down hret) F H.hKD
        hP hZ hxl0 hyl0 (by rw [← hm01]; exact hodd) hm1 e1 (e2.trans hDsp) e3 ((e5.trans hD28).trans h28) e6 f1 f2 f3
        (by rw [e4, hD18, e5, hD28]; exact hE)
    · intro _ hev0 S' e1 e2 e3 e4 e5 e6 e7
      rw [← e7] at hZ f1 f2 f3
      have hm0 : s.mem.readLE mp 8 % 2 = 0 := by rw [← hm01]; exact hev0
      by_cases hpow : ∃ k, natVal s.mem mp n = 2 ^ k
      · exact liftNE impl hap <| p2Path impl hap R H.p2 H.hnsP H.hn11P ret0 (retAddr_down hret) F hP hX H.hKP hZ hxl0
          hyl0 hpow hm0 e1 (e2.trans hDsp) e3 e4 ((e6.trans hD28).trans h28) f1 f2 f3
          (by rw [e5, hD18, e6, hD28]; exact hE)
      · exact evPath impl hap R hEv ret0 hret F hP hX hstkE hnE hcE hZ hxl0 hyl0 hy1 hpow hm0 e1 (e2.trans hDsp) e3 e4
          ((e6.trans hD28).trans h28) f1 f2 f3 (by rw [e5, hD18, e6, hD28]; exact hE)
  refine mkE impl R (MakesliceLiveContract.of_codeIn (codeInNE impl hap) H.mkN) ret0 hret _ b L K g sp zc' st n M hal hK4 hKs hsp2
    (by rw [hF.accessible]; exact hacc) hg1 (by rw [hF.accessible]; exact hg2)
    (by rw [hF.readLE _ _ hgw]; exact hg3) hout (by unfold Apart; omega) hgo.2 hLs
    (dataLoaded_frame hd hrg hro hF' (fun r hr _ => by
      simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)))
    hro hty hzc' (by omega) hn (by omega)
    (fun _ => ⟨hsv.1 _ _ _ (by omega), by omega⟩) hinvM S hpc hSsp h2 h3 h11 (h28.trans hs28) hmem ?_ ?_
  · intro hle S' e1 e2 e0 e2' e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e18 e28 em
    have hz' : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g sp K st zp zc xp xl yp yl mp n s.mem)) ∨
        (zp' = 0 ∧ zc' = 0) := hz
    refine tgt S' M L b zp' zc' 0 (zm_keep hP hF hLF hrg hz' hle) h29v h30v hsl
      (by rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) (e2.trans hSsp)
      ⟨e0.trans h0, Or.inl ⟨e1, e2'.trans h2, e3.trans h3, e4.trans h4, e5.trans h5, e6.trans h6, e7.trans h7,
        e8.trans h8, e9.trans h9, e10.trans h10, e11.trans h11, e12.trans h12, e13.trans h13⟩⟩ em e18 e28
  · intro hlt S' p r m hpcs e2 e0 e18 e28 em h232 hLF' hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv'
    have hZ := zm_fresh hP hF' hLF hrg hLF' hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv'
    have kp : ∀ {a k : Nat}, (sp + 1048 ≤ a ∧ a + k ≤ sp + 1064) ∨ (sp + 1176 ≤ a ∧ a + k ≤ sp + 1184) ∨
        (sp + 1352 ≤ a ∧ a + k ≤ sp + 1432) ∨ (sp + 1272 ≤ a ∧ a + k ≤ sp + 1288) ∨
        (sp + 1296 ≤ a ∧ a + k ≤ sp + 1304) → m.readLE a k = M.readLE a k := fun h => by
      refine hMF.readLE _ _ ?_
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      rcases h with h | h | h | h | h
      · exact hout.of_sub (by omega) (by omega)
      · exact hout.of_sub (by omega) (by omega)
      · exact hout.of_sub (by omega) (by omega)
      · exact hout.of_sub (by omega) (by omega)
      · exact hout.of_sub (by omega) (by omega)
    have hsp' : Spills m sp st xp xl xc yp yl yc mp n mc :=
      spills_fr hsp h232 fun a k h1 h2 => kp (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    refine tgt S' m _ _ p (makeCap n) r hZ (by rw [kp (by omega)]; exact h29v) (by rw [kp (by omega)]; exact h30v)
      (hsl.of_rd fun a k hs => kp (by unfold Slot at hs; omega))
      (by rw [hMF.accessible, hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega))
      (e2.trans hSsp) ⟨e0, ?_⟩ em e18 e28
    rcases hpcs with ⟨hpc1, rfl⟩ | ⟨hpc2, hn1, h128⟩
    · exact Or.inr (Or.inl ⟨hpc1, rfl, rfl, em ▸ hsp'⟩)
    · refine Or.inr (Or.inr ⟨hpc2, ?_, em ▸ hsp'⟩)
      rw [em, h128]; unfold makeCap; rw [if_neg hn1]

end FvModexp.Arm64.ExpN
