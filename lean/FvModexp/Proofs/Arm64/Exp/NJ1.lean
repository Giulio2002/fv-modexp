import FvModexp.Proofs.Arm64.Exp.NMid
import FvModexp.Proofs.Arm64.Exp.NRemP
import FvModexp.Proofs.Arm64.Exp.NOne
import FvModexp.Proofs.Arm64.Exp.NTriv

/-!
# `nat.expNN` (arm64): from `J1` (fn+0x8c, after the prologue and the alias test) to expNN's return

`fromJ1`: `NTriv.triv` (`m == 1` / `x == 0 < y` → `z[:0]`: `post_triv`; `y == 0` / `x == 1` → `NOne.one`:
`post_oneA` / `post_oneB`), else `NStk.stk` (`y == 1` → `remPath`; otherwise `fromJ5`).
`z` (`X0..X2 = zp', zl', zc'`) is the entry `z` (kept by the alias test) or `nil` (`ZKeep`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- `z` after the alias test: kept (with `ZOK` if non-empty) or `nil` (hidden from `omega`) -/
def ZKeep (R : RtInv) (L : List (Nat × Nat)) (g sp K st zp zl zc xp xl yp yl mp n zp' zl' zc' : Nat) (M : Memory) :
    Prop :=
  (zp' = zp ∧ zl' = zl ∧ zc' = zc ∧ (0 < zc → ZOK R L g sp K st zp zc xp xl yp yl mp n M)) ∨
    (zp' = 0 ∧ zl' = 0 ∧ zc' = 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fromJ1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 zp' zl' zc' : Nat}
    {s : State}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hev : NoEvenB s.mem mp n)
    (hz : ZKeep R L g sp K st zp zl zc xp xl yp yl mp n zp' zl' zc' s.mem)
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
      Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, hd, hsv⟩, -, -, hro, hty, hslow,
    hn, hn128, -, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyc, hxO, hxa, hx48, -, hxl, hxp, hxc, hzp, hzlc,
    hzc, -, -, -, hst0, hst48, hsok, hstw, -, -, -, -, -, -, -, -, -, -, -, hbud, hinv⟩ := hP'
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
  have hm0M : M.readLE mp 8 = s.mem.readLE mp 8 := rdw (by have := hmO.2.1; unfold Apart at this ⊢; omega)
  have hx0M : 0 < xl → M.readLE xp 8 = s.mem.readLE xp 8 := fun h =>
    rdw (by have := hxO.2.1; unfold Apart at this ⊢; omega)
  have hy0M : 0 < yl → M.readLE yp 8 = s.mem.readLE yp 8 := fun h =>
    rdw (by have := hyO.2.1; unfold Apart at this ⊢; omega)
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hFw (fun r hr => Or.inr (out_rt_wN hwrt r hr)) hinv
  have hinvs : R.inv b L (s.regs 28).toNat (view R.rt L s.mem) := by rw [hg]; exact hinv
  have hzc' : zc' < 2 ^ 40 := by rcases hz with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩ <;> omega
  have hzp' : zp' < 2 ^ 64 := by rcases hz with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  have hS28 : S.regs 28 = BitVec.ofNat 64 g := h28.trans hs28
  refine triv impl ret0 hret F sp f29 xp xl yl mp n M hal (by omega) hsp2
    (by rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) (by omega) (by omega)
    (by omega) hxp (by omega)
    (fun h => by rw [hF.accessible]; exact Memory.accessible_mono _ hma (by omega) (by omega))
    (fun h => by rw [hF.accessible]; exact Memory.accessible_mono _ hxa (by omega) (by omega))
    h29v h30v S hpc hsp h4 h5 h8 h10 h11 hmem ?F0 ?K1 ?K2
  case F0 =>
    intro hc s' e1 e2 e3 e4 e5 e6 e7 hF2 hrg2
    refine hK' s' e1 e2 e6 e7 (post_triv hs hLs hwrt hsok hstw hinvs ?_ hzc ?_ ?_ (e3.trans h0) e4 (e5.trans h2))
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
      (dataLoaded_frame hd hrg hro (hFw.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) (fun r hr _ => by
        simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)))
      hro hty (by omega) hzp' ?_ (fun _ => ⟨hsv.1 _ _ _ (by omega), by omega⟩) hinvM h29v h30v T e1 (e2.trans hsp)
      (e3.trans h0) (e4.trans h2) e5 (e6.trans hS28) e7 ?FA ?FB
    · intro hc
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨-, hw, -, -⟩, ha, h48, -⟩ := hk hc
        exact ⟨by rw [hF.accessible]; exact Memory.accessible_mono _ ha (by omega) (by omega), by omega,
          Apart.mono hw (by omega) (Nat.le_refl _)⟩
      · omega
    case FA =>
      intro hc s' f1 f2 f3 f4 f5 f6 f7 hF2 hv1 hrg2
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨hH, -, hzs, -⟩, -, -, -, hzL, -⟩ := hk hc
        refine hK' s' f1 f2 f6 (f7.trans hS28.symm) (post_oneA hs hLs hwrt hsok hstw hinvs hc hzc hH hzs hzL hv ?_
          hv1 f3 f4 f5)
        exact hFw.trans hF2 fun a k ho => ⟨by rw [List.cons_append, outside_cons] at ho; exact ho.2,
          by simp only [wN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      · omega
    case FB =>
      intro hc s' p r m hLF hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv' f1 f2 f3 f4 f5 f6 f7 hF2 hv1 hrg2
      exact hK' s' f1 f2 f6 (f7.trans hS28.symm) (post_oneB hs hK4 hLs hwrt hsok hstw hv hFw hLF hMF hAp hIn hp48
        haccp hp8 hr8 hr (by rw [hg]; exact hinv') hF2 hv1 f3 f4 f5)
  case K2 =>
    intro hm1 hy0 hx0 hx1 T tpc tsp t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t18 t28 tm
    rw [hm0M] at hm1
    have hyo : yp + 8 ≤ sp + 1182 ∨ sp + 1425 ≤ yp := by have := hyO.2.1; unfold Apart at this; omega
    refine stk impl ret0 hret (IsReturn F) sp yp yl n st M hal (by omega) hsp2
      (by rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) (by omega) (by omega)
      (by omega) hn hst0 hy0 (by omega)
      (by rw [hF.accessible]; exact Memory.accessible_mono _ hya (by omega) (by omega)) hyo T tpc (tsp.trans hsp)
      (t3.trans h3) (t7.trans h7) (t8.trans h8) (t11.trans h11) tm ?KR ?KD
    case KR =>
      intro hy1 hyv U M2 upc usp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u18 u28 u30 um hF2 hrg2 hfl2
      have hFU : MemFrame s.mem U.mem (wN sp K) := um ▸ hFw.trans hF2 fun a k ho =>
        ⟨ho, by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      have hk2 : ∀ {a}, (a = sp + 1048 ∨ a = sp + 1056) → M2.readLE a 8 = M.readLE a 8 := fun h =>
        hF2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      refine remPath impl hap R hRem hnsR hn11R ret0 hret F hP hKR hFU (by rw [um, hrg2, hrg]) hz
        ⟨hy1, by rw [← hy0M (by omega)]; exact hyv⟩ upc (usp.trans (tsp.trans hsp)) (u0.trans (t0.trans h0))
        (u1.trans (t1.trans h1)) (u2.trans (t2.trans h2)) (u3.trans (t3.trans h3)) (u4.trans (t4.trans h4))
        (u5.trans (t5.trans h5)) (u6.trans (t6.trans h6)) (u7.trans (t10.trans h10)) (u8.trans (t11.trans h11))
        (u9.trans (t12.trans h12)) (u28.trans (t28.trans h28)) u30
        (by rw [um, hk2 (Or.inl rfl)]; exact h29v) (by rw [um, hk2 (Or.inr rfl)]; exact h30v) (by rw [um]; exact hfl2)
        (fun s'' a1 a2 a3 a4 hq => hK' s'' a1 a2 (a3.trans (u18.trans t18)) (a4.trans (u28.trans t28)) hq)
    case KD =>
      intro hny U M2 upc usp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u18 u28 um hF2 hrg2 hfl2
        r296 r304 r312 r320 r328 r336 r344 r352 r360 r368
      have hFU : MemFrame s.mem M2 (wN sp K) := hFw.trans hF2 fun a k ho =>
        ⟨ho, by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      have hk2 : ∀ {a}, (a = sp + 1048 ∨ a = sp + 1056) → M2.readLE a 8 = M.readLE a 8 := fun h =>
        hF2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      have hspl : SpillsB M2 sp xp xl xc yp yl yc mp n mc := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [r296, t4, h4]; exact tN' hxp
        · rw [r304, t5, h5]; exact tN' (by omega)
        · rw [r312, t6, h6]; exact tN' hxc
        · rw [r320, t7, h7]; exact tN' (by omega)
        · rw [r328, t8, h8]; exact tN' (by omega)
        · rw [r336, t9, h9]; exact tN' hyc
        · rw [r344, t10, h10]; exact tN' (by omega)
        · rw [r352, t11, h11]; exact tN' (by omega)
        · rw [r360, t12, h12]; exact tN' (by omega)
        · rw [r368, t13, h13, hslow]; rfl
      have hzJ : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g sp K st zp zc xp xl yp yl mp n s.mem)) ∨
          (zp' = 0 ∧ zc' = 0) := by
        rcases hz with ⟨a, -, c, d⟩ | ⟨a, -, c⟩
        · exact Or.inl ⟨a, c, d⟩
        · exact Or.inr ⟨a, c⟩
      refine fromJ5 impl hap R H ret0 hret F hP hzJ hx0 hy0 ?_ hm1 hev U M2 upc (usp.trans (tsp.trans hsp))
        (u0.trans (t0.trans h0)) (u2.trans (t2.trans h2)) (u3.trans (t3.trans h3)) (u4.trans (t4.trans h4))
        (u5.trans (t5.trans h5)) (u6.trans (t6.trans h6)) (u7.trans (t7.trans h7)) (u8.trans (t8.trans h8))
        (u9.trans (t9.trans h9)) (u10.trans (t10.trans h10)) (u11.trans (t11.trans h11))
        (u12.trans (t12.trans h12)) (by rw [u13, t13, h13, hslow]) (u28.trans (t28.trans h28)) um hFU
        (by rw [hrg2, hrg]) hspl (by rw [hk2 (Or.inl rfl)]; exact h29v) (by rw [hk2 (Or.inr rfl)]; exact h30v) hfl2
        (fun s'' a1 a2 a3 a4 hq => hK' s'' a1 a2 (a3.trans (u18.trans t18)) (a4.trans (u28.trans t28)) hq)
      rw [← hy0M (by omega)]; exact hny

end FvModexp.Arm64.ExpN
