import FvModexp.Proofs.Amd64.Exp.NNilSK
import FvModexp.Proofs.Amd64.Exp.NNilQ
import FvModexp.Proofs.Amd64.Exp.NTrivE
import FvModexp.Proofs.Amd64.Exp.NJ1

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: from `J1` to the return (agent expmc s75; twin of `Arm64.ExpN.fromJ1NE`)

`fromJ1NE`: `J1` (`0x5e7078`, after the alias test, memory `M`) → the trivial cases (`trivE`: `postN_triv`, the
`z = 1` cases via `one` lifted to `LibNE`: `postN_oneA` / `postN_oneB`) | `J2` with `stk == nil` (`nilK2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fromJ1NE (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hget : PoolGetLive (LibNE.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
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
      mc slow s) (hX : NHyp.XFacts R L xp xl xc) (hEv : EvH impl R K needS costS xl yl n)
    (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem) (hna : NHyp.NoAlias zp' zc' xp xc)
    (S : State) (M : Memory) (hpc : S.rip = BitVec.ofNat 64 6189176) (hsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h3 : S.regs 3 = BitVec.ofNat 64 zl') (h1 : S.regs 1 = BitVec.ofNat 64 zc')
    (h7 : S.regs 7 = BitVec.ofNat 64 st0) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = BitVec.ofNat 64 slow)
    (h2 : S.regs 2 = BitVec.ofNat 64 yc) (h12 : S.regs 12 = BitVec.ofNat 64 yp)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hmem : S.mem = M) (hF : MemFrame s.mem M [(sp + 0x390, sp + 0x498), (sp + 0x4d0, sp + 0x4f8)])
    (hrg : M.regions = s.mem.regions)
    (hbp : M.readLE (sp + 0x490) 8 = bp) (hrv : M.readLE (sp + 0x498) 8 = ret0)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = S.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, hK1, hK2, hce, hsv⟩, -, -, hty, -, -, hslow, hry, hryl, hryc, hrm, hrn, hrmc,
    hn, hn128, -, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyc, hxO, hxa, hx48, hxN, hxl, hxlc, hxc, hzp,
    ⟨hzlc, hxz, hxlz, hxcz⟩, hzc, -, -, -, -, hst0, -, -, -, -, -, hbud, -, hinv, -⟩ := hP'
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
  have hm0M : M.readLE mp 8 = s.mem.readLE mp 8 := rdw (by have := hmO.2; unfold Apart at this ⊢; omega)
  have hx0M : 0 < xl → M.readLE xp 8 = s.mem.readLE xp 8 := fun h =>
    rdw (by have := (hxO h).2; unfold Apart at this ⊢; omega)
  have hy0M : 0 < yl → M.readLE yp 8 = s.mem.readLE yp 8 := fun h =>
    rdw (by have := (hyO h).2; unfold Apart at this ⊢; omega)
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hFw (fun r hr => Or.inr (wN_rt (rw_of hK0 hwrt) r hr)) hinv
  have hinvs : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := by rw [hg]; exact hinv
  have hzc' : zc' < 2 ^ 40 := by rcases hz with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩ <;> omega
  have hzp' : zp' < 2 ^ 64 := by rcases hz with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  have hsp' : S.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := hsp.trans (congrArg _ (by omega))
  have hacc' : M.accessible (sp + 0x498 - 0x110) 0x188 true = true := by
    rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have rbp : M.readLE (sp + 0x498 - 8) 8 = bp := by rw [show sp + 0x498 - 8 = sp + 0x490 by omega]; exact hbp
  refine trivE impl ret0 hret F (sp + 0x498) bp xp xl yl mp n M (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc' (by omega) (by omega)) (by omega) (by subst hxz; omega)
    (fun h => by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hma (Or.inl rfl) (by omega) (by omega))
    (fun h => by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ (hxa h) (by omega) (by omega))
    rbp hrv (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x10 = sp + 0x4a8 by omega]; exact hryl)
    (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x20 = sp + 0x4b8 by omega]; exact hrm)
    (by rw [rda (by omega) (by omega), show sp + 0x498 + 0x28 = sp + 0x4c0 by omega]; exact hrn)
    S hpc hsp' h6 h8 hmem ?F0 ?K1 ?K2
  case F0 =>
    intro hc s' e4 e5 e0 e3 e1 e14 efs edf ex hF2 _
    refine hK' s' e4 e5 e14 (ex.trans hx15) (postN_triv hs hK0 hLs hwrt hinvs ?_ hzc hzp ?_
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
    refine liftNE impl hap (one impl R H.mkN ret0 (retAddr_down hret) F b L K g fs (sp + 0x498) bp zp' zc' pc0 M hpc0
      (by rw [show sp + 0x498 - 0x498 = sp by omega]; exact ce1) (by omega) (by omega) hty (by omega) hzp' ?_
      (fun _ => ⟨hsv.1 _ _ _ (by decide), by omega⟩) hinvM rbp hrv T e_rip (e4.trans hsp') (e0.trans h0) (e1.trans h1)
      (e14.trans hS14) (by rw [efs, hfs]; exact hsfs) (ex15.trans hx15) (by rw [edf, hdf]; exact hsdf) em ?FA ?FB)
    · intro hc
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨-, hw⟩, ha, h48, -⟩ := hk hc
        exact ⟨by rw [hFw.accessible]; exact Janus.Arm64.Memory.accessible_mono _ ha (by omega) (by omega), by omega,
          by rw [show sp + 0x498 - 0x498 = sp by omega]; exact Apart.mono hw (by omega) (Nat.le_refl _)⟩
      · omega
    case FA =>
      intro hc s' f4 f5 f0 f3 f1 f14 ffs fdf fx hF2 hv1 _
      rcases hz with ⟨rfl, -, rfl, hk⟩ | ⟨-, -, rfl⟩
      · obtain ⟨⟨hH, -⟩, -, -, -, hzL, -⟩ := hk hc
        refine hK' s' f4 f5 (f14.trans hS14.symm) (fx.trans (ex15.trans hx15))
          (postN_oneA hs hK0 hLs hwrt hinvs hc hzc hH hzL hv ?_ hv1 f0 f3 f1 (by rw [ffs, efs, hfs])
            (by rw [fdf, edf, hdf]))
        exact hFw.trans hF2 fun a k ho => ⟨by rw [List.cons_append, outside_cons] at ho; exact ho.2,
          by simp only [wN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
      · omega
    case FB =>
      intro hc s' p r m hLF hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv' f4 f5 f0 f3 f1 f14 ffs fdf fx hF2 hv1 _
      exact hK' s' f4 f5 (f14.trans hS14.symm) (fx.trans (ex15.trans hx15)) (postN_oneB hs hK1 hK0 hLs hwrt hv hFw hLF
        hMF hAp hIn hp48 haccp hp8 hr8 hr (by rw [hg]; exact hinv') hF2 hv1 f0 f3 f1 (by rw [ffs, efs, hfs])
        (by rw [fdf, edf, hdf]))
  case K2 =>
    intro hm1 hy0 hx0 hx1 T tpc tsp t0 t3 t1 t7 t6 t8 t9 t10 t2 t12 t5 t15 t13 t11 t14 tfs tdf tx15 tm
    rw [hm0M] at hm1
    exact nilK2 impl hap R hput hget hno H hRem hnsR hnfR hKR ret0 hret F hP hX hz hna hx0 hy0 hm1 hEv
      (fun s'' a4 a5 a14 ax hq => hK' s'' a4 a5 (a14.trans h14.symm) ax hq) M hF hrg hbp hrv T tpc (tsp.trans hsp)
      (t0.trans h0) (t3.trans h3) (t1.trans h1) (t7.trans h7) (t6.trans h6) (t8.trans h8) (t9.trans h9)
      (t10.trans h10) (t12.trans h12) t15 t11 (t14.trans h14) (tfs.trans hfs) (tdf.trans hdf) (tx15.trans hx15) tm

end FvModexp.Amd64.ExpN
