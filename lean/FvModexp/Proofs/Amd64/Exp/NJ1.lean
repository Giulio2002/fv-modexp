import FvModexp.Proofs.Amd64.Exp.NMidM
import FvModexp.Proofs.Amd64.Exp.NPost
import FvModexp.Proofs.Amd64.Exp.NOne
import FvModexp.Proofs.Amd64.Exp.NTriv

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): from `J1` (`0x5e7078`, after the prologue and the alias test) to expNN's return (agent expmc
s72; twin of `Arm64.ExpN.fromJ1`)

`fromJ1`: `NTriv.triv` (`m == 1` / `x == 0 < y` → `z[:0]`: `post_triv`; `y == 0` / `x == 1` → `NOne.one`:
`post_oneA` / `post_oneB`), else `NStk.stk` (`y == 1` → `remPath`; otherwise `fromJ4`). `z` (`RAX, RBX, RCX = zp',
zl', zc'`) is the entry `z` (kept by the alias test) or `nil` (`ZKeep`). `t = sp + 0x498` is the entry `RSP`; the
prologue's writes are a frame `[t - 0x108, t) ∪ [t + 0x38, t + 0x60)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `z` after the alias test: kept (with `ZOK` if non-empty) or `nil` (hidden from `omega`) -/
def ZKeep (R : RtInv) (L : List (Nat × Nat)) (g fs sp K st zp zl zc xp xc yp yl mp n zp' zl' zc' : Nat) (M : Memory) :
    Prop :=
  (zp' = zp ∧ zl' = zl ∧ zc' = zc ∧ (0 < zc → ZOK R L g fs sp K st zp zc xp xc yp yl mp n M)) ∨
    (zp' = 0 ∧ zl' = 0 ∧ zc' = 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fromJ1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp zp' zl' zc' : Nat}
    {s : State}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hX : NHyp.XFacts R L xp xl xc) (hev : NoEvenB s.mem mp n)
    (hz : ZKeep R L g fs sp K st zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem)
    (hna : NHyp.NoAlias zp' zc' xp xc)
    (S : State) (M : Memory) (hpc : S.rip = BitVec.ofNat 64 6189176) (hsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h3 : S.regs 3 = BitVec.ofNat 64 zl') (h1 : S.regs 1 = BitVec.ofNat 64 zc')
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = BitVec.ofNat 64 slow)
    (h2 : S.regs 2 = BitVec.ofNat 64 yc) (h12 : S.regs 12 = BitVec.ofNat 64 yp)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hmem : S.mem = M) (hF : MemFrame s.mem M [(sp + 0x390, sp + 0x498), (sp + 0x4d0, sp + 0x4f8)])
    (hrg : M.regions = s.mem.regions)
    (hbp : M.readLE (sp + 0x490) 8 = bp) (hrv : M.readLE (sp + 0x498) 8 = ret0)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = S.regs 14 → Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, hK1, hK2, hce, hsv⟩, -, hty, -, -, hslow, hry, hryl, hryc, hrm, hrn, hrmc,
    hn, hn128, -, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyc, hxO, hxa, hx48, hxN, hxl, hxlc, hxc, hzp,
    hzlc, hzc, -, -, -, hst0, hst48, hsok, hstw, -, -, -, -, -, -, -, -, -, -, -, -, -, hbud, -, hinv, -⟩ := hP'
  have hce0 := hce
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hwrt, hga, hgrt, hLs, -, -, f1, f2, f3, f4, f5, f6⟩ := hce0
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hg : (s.regs 14).toNat = g := by rw [hs14, BitVec.toNat_ofNat]; omega
  have hFw : MemFrame s.mem M (wN sp K) := hF.mono fun a k ho => by
    simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rdw : ∀ {a k : Nat}, Apart a k (sp - K) (K + 0x510) → M.readLE a k = s.mem.readLE a k := fun h =>
    hF.readLE _ _ (by unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega)
  have rda : ∀ {a k : Nat}, sp + 0x498 ≤ a → a + k ≤ sp + 0x4d0 → M.readLE a k = s.mem.readLE a k := fun h1 h2 =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hm0M : M.readLE mp 8 = s.mem.readLE mp 8 := rdw (by have := hmO.2.1; unfold Apart at this ⊢; omega)
  have hx0M : 0 < xl → M.readLE xp 8 = s.mem.readLE xp 8 := fun h =>
    rdw (by have := hxO.2.1; unfold Apart at this ⊢; omega)
  have hy0M : 0 < yl → M.readLE yp 8 = s.mem.readLE yp 8 := fun h =>
    rdw (by have := hyO.2.1; unfold Apart at this ⊢; omega)
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hFw (fun r hr => Or.inr (wN_rt (rw_of hK0 hwrt) r hr)) hinv
  have hinvs : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := by rw [hg]; exact hinv
  have hzc' : zc' < 2 ^ 40 := by rcases hz with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩ <;> omega
  have hzp' : zp' < 2 ^ 64 := by rcases hz with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  have hsp' : S.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := hsp.trans (congrArg _ (by omega))
  have hacc' : M.accessible (sp + 0x498 - 0x110) 0x188 true = true := by
    rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have rbp : M.readLE (sp + 0x498 - 8) 8 = bp := by rw [show sp + 0x498 - 8 = sp + 0x490 by omega]; exact hbp
  refine triv impl ret0 hret F (sp + 0x498) bp xp xl yl mp n M (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc' (by omega) (by omega)) (by omega) (by omega)
    (fun h => by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hma (Or.inl rfl) (by omega) (by omega))
    (fun h => by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hxa (by omega) (by omega))
    rbp hrv (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x10 = sp + 0x4a8 by omega]; exact hryl)
    (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x20 = sp + 0x4b8 by omega]; exact hrm)
    (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x28 = sp + 0x4c0 by omega]; exact hrn)
    S hpc hsp' h6 h8 hmem ?F0 ?K1 ?K2
  case F0 =>
    intro hc s' e4 e5 e0 e3 e1 e14 efs edf _ hF2 _
    refine hK' s' e4 e5 e14 (post_triv hs hK0 hLs hwrt hsok hstw hinvs ?_ hzc hzp ?_
      (hFw.trans hF2 fun a k ho => ⟨ho, by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩)
      (e0.trans h0) e3 (e1.trans h1) (efs.trans hfs) (edf.trans hdf))
    · rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨rfl, -, rfl⟩
      · exact Or.inl ⟨rfl, rfl, fun h => (hk h).2.2.2.2.1 h⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · refine val_triv hyN ?_
      rw [hm0M] at hc
      rcases hc with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
  case K1 =>
    intro hm1 hyx T pc0 hpc0 e_rip e4 e0 e1 e14 efs edf ex15 em
    rw [hm0M] at hm1
    have hM1 := m_gt1 hn hmN hm1
    have hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1 := by
      refine val_one hM1 ?_
      rcases hyx with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by rw [← hx0M (by omega)]; exact h2⟩
    have hbl := blockSize_le_allocCost 8 true
    have e1c : makeCost 1 = allocCost 8 := rfl
    have hws : ∀ r ∈ [(sp + 0x390, sp + 0x498), (sp + 0x4d0, sp + 0x4f8)], r.1 < r.2 →
        s.mem.accessible r.1 (r.2 - r.1) true = true := by
      intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    have ce1 := CallW.CEnv.frame hce (hF.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) hrg hws
      (by unfold Apart at hga; simp only [outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at f6; simp only [outside_cons, outside_nil, and_true]; omega)
    have hS14 : S.regs 14 = BitVec.ofNat 64 g := h14.trans hs14
    refine one impl R H.mkN ret0 hret F b L K g fs (sp + 0x498) bp zp' zc' pc0 M hpc0
      (by rw [show sp + 0x498 - 0x498 = sp by omega]; exact ce1) (by omega) (by omega) hty (by omega) hzp' ?_
      (fun _ => ⟨hsv.1 _ _ _ (by decide), by omega⟩) hinvM rbp hrv T e_rip (e4.trans hsp') (e0.trans h0) (e1.trans h1)
      (e14.trans hS14) (by rw [efs, hfs]; exact hsfs) (ex15.trans hx15) (by rw [edf, hdf]; exact hsdf) em ?FA ?FB
    · intro hc
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨-, hw, -, -⟩, ha, h48, -⟩ := hk hc
        exact ⟨by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ ha (by omega) (by omega), by omega,
          by rw [show sp + 0x498 - 0x498 = sp by omega]; exact Apart.mono hw (by omega) (Nat.le_refl _)⟩
      · omega
    case FA =>
      intro hc s' f4 f5 f0 f3 f1 f14 ffs fdf _ hF2 hv1 _
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨hH, -, hzs, -⟩, -, -, -, hzL, -⟩ := hk hc
        refine hK' s' f4 f5 (f14.trans hS14.symm) (post_oneA hs hK0 hLs hwrt hsok hstw hinvs hc hzc hH hzs hzL hv ?_
          hv1 f0 f3 f1 (by rw [ffs, efs, hfs]) (by rw [fdf, edf, hdf]))
        exact hFw.trans hF2 fun a k ho => ⟨by rw [List.cons_append, outside_cons] at ho; exact ho.2,
          by simp only [wN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      · omega
    case FB =>
      intro hc s' p r m hLF hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv' f4 f5 f0 f3 f1 f14 ffs fdf _ hF2 hv1 _
      exact hK' s' f4 f5 (f14.trans hS14.symm) (post_oneB hs hK1 hK0 hLs hwrt hsok hstw hv hFw hLF hMF hAp hIn hp48
        haccp hp8 hr8 hr (by rw [hg]; exact hinv') hF2 hv1 f0 f3 f1 (by rw [ffs, efs, hfs]) (by rw [fdf, edf, hdf]))
  case K2 =>
    intro hm1 hy0 hx0 hx1 T tpc tsp t0 t3 t1 t7 t6 t8 t9 t10 t2 t12 t5 t15 t13 t11 t14 tfs tdf tx15 tm
    rw [hm0M] at hm1
    have hyo : yp + 8 ≤ sp + 0x498 - 0x110 ∨ sp + 0x498 + 0x78 ≤ yp := by
      have := hyO.2.1; unfold Apart at this; omega
    refine stk impl ret0 hret (IsReturn F) (sp + 0x498) yp yl mp n mc st M (by omega) (by omega) hacc'
      (by omega) (by omega) (by omega) (by omega) hn hst0 hy0 (by omega)
      (by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hya (by omega) (by omega)) hyo
      (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x30 = sp + 0x4c8 by omega]; exact hrmc) T tpc
      (tsp.trans hsp') (t7.trans h7) (t12.trans h12) t15 t11 t13 tm ?KR ?KD
    case KR =>
      intro hy1 hyv U M2 upc usp u0 u3 u1 u7 u6 u8 u9 u5 u14 ufs udf ux15 um hF2 hrg2 hra q0 q1 q2 hfl _ _ _ _
      subst um
      have hFU : MemFrame s.mem U.mem (wN sp K) := hFw.trans hF2 fun a k ho =>
        ⟨ho, by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      have kf : ∀ {a}, (a = sp + 0x490 ∨ a = sp + 0x498) → U.mem.readLE a 8 = M.readLE a 8 := fun h =>
        hF2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      refine remPath impl hap R hRem hnsR hnfR ret0 hret F hP hKR hFU (by rw [hrg2, hrg]) hz hna
        ⟨hy1, by rw [← hy0M (by omega)]; exact hyv⟩ upc (usp.trans (congrArg _ (by omega)))
        (u0.trans (t0.trans h0)) (u3.trans (t3.trans h3)) (u1.trans (t1.trans h1)) (u7.trans (t7.trans h7))
        (u6.trans (t6.trans h6)) (u8.trans (t8.trans h8)) (u9.trans (t9.trans h9)) (u14.trans (t14.trans h14))
        (ufs.trans (tfs.trans hfs)) (udf.trans (tdf.trans hdf)) (ux15.trans (tx15.trans hx15))
        (by rw [show sp + 0x388 = sp + 0x498 - 0x110 by omega]; exact hra)
        (by rw [show sp + 0x390 = sp + 0x498 - 0x108 by omega]; exact q0)
        (by rw [show sp + 0x398 = sp + 0x498 - 0x100 by omega]; exact q1)
        (by rw [show sp + 0x3a0 = sp + 0x498 - 0xf8 by omega]; exact q2)
        (by rw [kf (Or.inl rfl)]; exact hbp) (by rw [kf (Or.inr rfl)]; exact hrv) (SlotEq.refl _ _)
        (epiK0 impl ret0 hret F (sp + 0x498) bp _ U.mem _ (by omega) (by omega) hfl
          fun s'' a1 a2 a3 hq => hK' s'' a1 a2 (a3.trans (u14.trans t14)) hq)
    case KD =>
      intro hny U M2 upc usp u0 u3 u1 u7 u6 u8 u9 u10 u11 u12 u13 u15 u5 u2 u14 ufs udf ux15 um hF2 hrg2 hfl
        q58 q60 q68 q70
      subst um
      have hFU : MemFrame s.mem U.mem (wN sp K) := hFw.trans hF2 fun a k ho =>
        ⟨ho, by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      have kf : ∀ {a k : Nat}, (sp + 0x490 ≤ a ∧ a + k ≤ sp + 0x4d0) → U.mem.readLE a k = M.readLE a k := fun h =>
        hF2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      have ky : ∀ {a k v : Nat}, sp + 0x498 ≤ a → a + k ≤ sp + 0x4d0 → s.mem.readLE a k = v → U.mem.readLE a k = v :=
        fun h1 h2 hv => by rw [kf ⟨by omega, h2⟩, rda h1 h2]; exact hv
      have hslow0 : slow = 0 := hslow
      have hspl : SpillsB U.mem sp xp xl xc yp yl yc mp n mc := by
        refine ⟨ky (by omega) (by omega) hry, ky (by omega) (by omega) hryl, ky (by omega) (by omega) hryc,
          ky (by omega) (by omega) hrm, ky (by omega) (by omega) hrn, ky (by omega) (by omega) hrmc, ?_, ?_, ?_, ?_⟩
        · rw [show sp + 0x4f0 = sp + 0x498 + 0x58 by omega, q58, t6, h6]; exact tN' (by omega)
        · rw [show sp + 0x4f8 = sp + 0x498 + 0x60 by omega, q60, t8, h8]; exact tN' (by omega)
        · rw [show sp + 0x500 = sp + 0x498 + 0x68 by omega, q68, t9, h9]; exact tN' (by omega)
        · rw [show sp + 0x508 = sp + 0x498 + 0x70 by omega, q70, t10, h10, hslow0]; rfl
      have hzJ : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g fs sp K st zp zc xp xc yp yl mp n s.mem)) ∨
          (zp' = 0 ∧ zc' = 0) := by
        rcases hz with ⟨a, -, c, d⟩ | ⟨a, -, c⟩
        · exact Or.inl ⟨a, c, d⟩
        · exact Or.inr ⟨a, c⟩
      refine fromJ4 impl hap R H ret0 hret F hP hX hzJ hx0 hy0 ?_ hm1 hev U U.mem upc (usp.trans (tsp.trans hsp))
        (u0.trans (t0.trans h0)) (u1.trans (t1.trans h1)) (u2.trans (t2.trans h2)) (u7.trans (t7.trans h7))
        (u6.trans (t6.trans h6)) (u8.trans (t8.trans h8)) (u9.trans (t9.trans h9))
        (by rw [u10, t10, h10, hslow0]) (u11.trans t11) (u12.trans (t12.trans h12)) (u13.trans t13)
        (u15.trans t15) (u14.trans (t14.trans h14)) (ufs.trans (tfs.trans hfs)) (udf.trans (tdf.trans hdf))
        (ux15.trans (tx15.trans hx15)) rfl hFU (by rw [hrg2, hrg]) hspl
        (by rw [kf ⟨by omega, by omega⟩]; exact hbp) (by rw [kf ⟨by omega, by omega⟩]; exact hrv) (SlotEq.refl _ _)
        (epiK0 impl ret0 hret F (sp + 0x498) bp _ U.mem _ (by omega) (by omega) hfl
          fun s'' a1 a2 a3 hq => hK' s'' a1 a2 (a3.trans (u14.trans t14)) hq)
      rw [← hy0M (by omega)]; exact hny

end FvModexp.Amd64.ExpN
