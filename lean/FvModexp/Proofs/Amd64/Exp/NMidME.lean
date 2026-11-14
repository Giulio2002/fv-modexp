import FvModexp.Proofs.Amd64.Exp.NMidM
import FvModexp.Proofs.Amd64.Exp.NMidE
import FvModexp.Proofs.Amd64.Exp.NMkE
import FvModexp.Proofs.Amd64.Exp.NMkPE

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): from `J4` (the make) to expNN's return, every modulus (`fromJ4E`, on `LibNE`) (agent expmc s73)

`NMidM.fromJ4` on `LibNE` (`mkE`, `mkp1E`, `mkp2E`) ending in `fromJ5E` (the `expNNEven` path included, premise `EvH`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `J4` (the make of nat.go:694) to expNN's return -/
theorem fromJ4E (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp zp' zc' : Nat}
    {s : State}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hX : NHyp.XFacts R L xp xl xc)
    (hz : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g fs sp K st zp zc xp xc yp yl mp n s.mem)) ∨ (zp' = 0 ∧ zc' = 0))
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hEv : EvH impl R K needS costS xl yl n)
    (S : State) (M : Memory) (hpc : S.rip = BitVec.ofNat 64 6190084) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp') (h1 : S.regs 1 = BitVec.ofNat 64 zc') (h2 : S.regs 2 = BitVec.ofNat 64 yc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = 0#64) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h12 : S.regs 12 = BitVec.ofNat 64 yp) (h13 : S.regs 13 = BitVec.ofNat 64 mp)
    (h15 : S.regs 15 = BitVec.ofNat 64 yl)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hmem : S.mem = M) (hF : MemFrame s.mem M (wN sp K)) (hrg : M.regions = s.mem.regions)
    (hsp : SpillsB M sp xp xl xc yp yl yc mp n mc)
    (hbp : M.readLE (sp + 0x490) 8 = bp) (hrv : M.readLE (sp + 0x498) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq M M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, hK1, hK2, hce, hsv⟩, -, hty, -, -, -, -, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, -, hm48, -, hyO, -, hy48, -, hyl, -, hxO, -, hx48, -, hxl, hxlc, hxc, hzp, hzlc, hzc, -,
    -, -, hst0, hst48, hsok, hstw, -, -, -, -, -, -, -, -, -, -, -, -, -, hbud, -, hinv, -⟩ := hP'
  have hce0 := hce
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hwrt, hga, -, hLs, -, -, -, -, -, -, -, f6⟩ := hce0
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hsp
  have hF' : MemFrame s.mem M (R.rt ++ wN sp K) := hF.mono fun a k ho => by rw [outside_append] at ho; exact ho.2
  have hLF : LiveFrame s.mem M L [] := LiveFrame.of_win hF (liveSep_wN hLs)
  have hws : ∀ r ∈ wN sp K, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have ce1 := CallW.CEnv.frame hce hF' hrg hws
    (by unfold Apart at hga; simp only [wN, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [wN, outside_cons, outside_nil, and_true]; omega)
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hF (fun r hr => Or.inr (wN_rt (rw_of hK0 hwrt) r hr)) hinv
  have hzc' : zc' < 2 ^ 40 := by rcases hz with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> omega
  have hbl : blockSize (8 * makeCap n) true ≤ makeCost n := blockSize_le_allocCost _ _
  have hmc1 : makeCap n ≤ n + 4 := by unfold makeCap; split <;> omega
  have hS4 : S.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := hSsp.trans (congrArg _ (by omega))
  refine mkE impl R (MakesliceLiveContract64.of_codeIn (codeInNE impl hap) H.mkN) ret0 hret _ b L K g fs (sp + 0x498) zc' st n M
    (by rw [show sp + 0x498 - 0x498 = sp by omega]; exact ce1) (by omega) (by omega) hty hzc' (by omega) hn
    (by omega) (fun _ => ⟨hsv.1 _ _ _ (by omega), by omega⟩) hinvM S hpc hS4 h1 h7 h11 (h14.trans hs14)
    (by rw [hfs]; exact hsfs) hx15 (hdf.trans hsdf) hmem ?KU ?KA
  case KU =>
    intro hle S' e_rip e3 e0 e1 e2 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 efs edf ex15 em
    exact fromJ5E impl hap R H ret0 hret F hP hX hxl0 hyl0 hy1 hm1 hEv (zm_keep hP hF hLF hrg hz hle) S' e_rip
      (e4.trans hSsp) ⟨e0.trans h0, e1.trans h1, e7.trans h7, e6.trans h6, e8.trans h8, e9.trans h9, e10.trans h10,
        e12.trans h12, e15.trans h15, e2.trans h2, e3.trans h11, e11.trans h11, e13.trans h13⟩
      (e14.trans h14) (efs.trans hfs) (edf.trans hdf) (ex15.trans hx15) em p5 p4 hbp hrv hsl (by rw [e14]; exact hEk)
  case KA =>
    intro hlt S' p r m hpcs e4 e0 e14 efs edf ex15 em h18 hLF' hMF hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv'
    have hZ := zm_fresh hP hF' hLF hrg hLF' hMF (fun a k ho => by
      simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega) hrg' hAp hIn hp48 haccp hp8 hr8 hr hinv'
    have hW1 : Outside (sp - K) (K + 0x510) R.rt := hwrt
    have kp : ∀ {a k : Nat}, sp + 0x498 - 0x10 ≤ a → a + k ≤ sp + 0x510 → m.readLE a k = M.readLE a k :=
      fun h1 h2 => hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hW1.of_sub (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩)
    have hsl' : SlotEq m M0 (sp + 0x498) := hsl.of_rd fun a k hs => hMF.readLE _ _ (by
      unfold Slot at hs
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨hW1.of_sub (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩)
    have hacc' : S'.mem.accessible (sp + 0x498 - 0x108) 0x180 false = true := by
      rw [em, hMF.accessible, hF.accessible]
      exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
    have q2 : S'.mem.readLE (sp + 0x498 + 0x18) 8 = yc := by
      rw [em, show sp + 0x498 + 0x18 = sp + 0x4b0 by omega, kp (by omega) (by omega)]; exact p2
    have q3 : S'.mem.readLE (sp + 0x498 + 0x28) 8 = n := by
      rw [em, show sp + 0x498 + 0x28 = sp + 0x4c0 by omega, kp (by omega) (by omega)]; exact p4
    have q6 : S'.mem.readLE (sp + 0x498 + 0x58) 8 = xp := by
      rw [em, show sp + 0x498 + 0x58 = sp + 0x4f0 by omega, kp (by omega) (by omega)]; exact p6
    have q7 : S'.mem.readLE (sp + 0x498 - 0x18) 8 = st := by rw [em]; exact h18
    have q8 : S'.mem.readLE (sp + 0x498 + 0x60) 8 = xl := by
      rw [em, show sp + 0x498 + 0x60 = sp + 0x4f8 by omega, kp (by omega) (by omega)]; exact p7
    have q9 : S'.mem.readLE (sp + 0x498 + 0x68) 8 = xc := by
      rw [em, show sp + 0x498 + 0x68 = sp + 0x500 by omega, kp (by omega) (by omega)]; exact p8
    have q10 : S'.mem.readLE (sp + 0x498 + 0x70) 1 = 0 := by
      rw [em, show sp + 0x498 + 0x70 = sp + 0x508 by omega, kp (by omega) (by omega)]; exact p9
    have q12 : S'.mem.readLE (sp + 0x498 + 0x8) 8 = yp := by
      rw [em, show sp + 0x498 + 0x8 = sp + 0x4a0 by omega, kp (by omega) (by omega)]; exact p0
    have q13 : S'.mem.readLE (sp + 0x498 + 0x20) 8 = mp := by
      rw [em, show sp + 0x498 + 0x20 = sp + 0x4b8 by omega, kp (by omega) (by omega)]; exact p3
    have q15 : S'.mem.readLE (sp + 0x498 + 0x10) 8 = yl := by
      rw [em, show sp + 0x498 + 0x10 = sp + 0x4a8 by omega, kp (by omega) (by omega)]; exact p1
    have hmcm : m.readLE (sp + 0x4c8) 8 = mc := by rw [kp (by omega) (by omega)]; exact p5
    have hmnm : m.readLE (sp + 0x4c0) 8 = n := by rw [kp (by omega) (by omega)]; exact p4
    have hbpm : m.readLE (sp + 0x490) 8 = bp := by rw [kp (by omega) (by omega)]; exact hbp
    have hrvm : m.readLE (sp + 0x498) 8 = ret0 := by rw [kp (by omega) (by omega)]; exact hrv
    have e4' : S'.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := e4.trans hS4
    have hEk' : EpiK impl ret0 F (sp + 0x498) bp (S'.regs 14) M0
        (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s) := by rw [e14]; exact hEk
    have hJ : ∀ (D : State) (cx : Nat), D.regs 0 = S'.regs 0 → D.regs 1 = BitVec.ofNat 64 cx →
        D.regs 2 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x18) 8) →
        D.regs 3 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x28) 8) →
        D.regs 6 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x58) 8) →
        D.regs 7 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 - 0x18) 8) →
        D.regs 8 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x60) 8) →
        D.regs 9 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x68) 8) →
        D.regs 10 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x70) 1) → D.regs 11 = BitVec.ofNat 64 n →
        D.regs 12 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x8) 8) →
        D.regs 13 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x20) 8) →
        D.regs 15 = BitVec.ofNat 64 (S'.mem.readLE (sp + 0x498 + 0x10) 8) →
        J5S D p cx st xp xl xc yp yl yc mp n := by
      intro D cx d0 d1 d2 d3 d6 d7 d8 d9 d10 d11 d12 d13 d15
      exact ⟨d0.trans e0, d1, by rw [d7, q7], by rw [d6, q6], by rw [d8, q8], by rw [d9, q9], by rw [d10, q10],
        by rw [d12, q12], by rw [d15, q15], by rw [d2, q2], by rw [d3, q3], d11, by rw [d13, q13]⟩
    rcases hpcs with ⟨hpc1, hn1⟩ | ⟨hpc2, hn1, h90⟩
    · subst hn1
      refine mkp1E impl ret0 hret _ (sp + 0x498) (by omega) (by omega) S' hacc' hpc1 e4' ?_
      intro D d_rip d0 d1 d2 d3 d4 d6 d7 d8 d9 d10 d11 d12 d13 d15 d14 dfs ddf dx15 dm
      exact fromJ5E impl hap R H ret0 hret F hP hX hxl0 hyl0 hy1 hm1 hEv hZ D d_rip (d4.trans (e4.trans hSsp))
        (hJ D 1 d0 d1 d2 d3 d6 d7 d8 d9 d10 d11 d12 d13 d15) (d14.trans (e14.trans h14))
        (dfs.trans (efs.trans hfs)) (ddf.trans (edf.trans hdf)) (dx15.trans (ex15.trans hx15)) (dm.trans em)
        hmcm hmnm hbpm hrvm hsl' (by rw [d14]; exact hEk')
    · refine mkp2E impl ret0 hret _ (sp + 0x498) (by omega) (by omega) S' hacc' hpc2 e4' ?_
      intro D d_rip d0 d1 d2 d3 d4 d6 d7 d8 d9 d10 d11 d12 d13 d15 d14 dfs ddf dx15 dm
      have hcx : S'.mem.readLE (sp + 0x498 - 0x90) 8 = makeCap n := by
        rw [em, h90]; unfold makeCap; rw [if_neg hn1]
      exact fromJ5E impl hap R H ret0 hret F hP hX hxl0 hyl0 hy1 hm1 hEv hZ D d_rip (d4.trans (e4.trans hSsp))
        (hJ D (makeCap n) d0 (by rw [d1, hcx]) d2 d3 d6 d7 d8 d9 d10 (by rw [d11, q3]) d12 d13 d15)
        (d14.trans (e14.trans h14)) (dfs.trans (efs.trans hfs)) (ddf.trans (edf.trans hdf))
        (dx15.trans (ex15.trans hx15)) (dm.trans em) hmcm hmnm hbpm hrvm hsl' (by rw [d14]; exact hEk')

end FvModexp.Amd64.ExpN
