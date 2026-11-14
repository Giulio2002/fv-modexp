import FvModexp.Proofs.Amd64.Exp.SlowJ

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): **`segE`** — entry `fnE` → `KS` (`setJ`) (agent expmc s79; twin of arm64 `SlowPE`)

`runE` (stack guard, frame, spills, `CMPQ CX, R8; JL`): reuse (`len x ≤ cap z`, `dl_reuse`) / `makeslice(Word, 1, 1)`
(`len x = 1`) / `makeslice(Word, len x, len x + 4)` (`mkCall`, `dl_fresh`, `runM1` / `runMN`). The fresh capacity is
`makeCap (len x)`; the budget drops by at most `makeCost (len x)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the constant slots after the prologue's writes -/
theorem esl_of (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FWp sp)) (a1 : M.readLE (sp + 0x1a8) 8 = bp) (a2 : M.readLE (sp + 0x1e8) 8 = zp)
    (a3 : M.readLE (sp + 0x200) 8 = st) (a4 : M.readLE (sp + 0x208) 8 = xp) (a5 : M.readLE (sp + 0x210) 8 = xl)
    (a6 : M.readLE (sp + 0x218) 8 = xc) : ESl M sp st bp r zp xp xl xc yp yl yc mp ml mc := by
  obtain ⟨-, hr1, -, hy1, hy2, hy3, hm1, hm2, hm3⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have k : ∀ a, sp + 0x1b0 ≤ a → a + 8 ≤ sp + 0x1e8 → M.readLE a 8 = s.mem.readLE a 8 := fun a h1 h2 =>
    hF.readLE a 8 (by simp only [FWp, outside_cons, outside_nil, and_true]; omega)
  exact ⟨a1, (k _ (by omega) (by omega)).trans hr1, (k _ (by omega) (by omega)).trans hy1,
    (k _ (by omega) (by omega)).trans hy2, (k _ (by omega) (by omega)).trans hy3,
    (k _ (by omega) (by omega)).trans hm1, (k _ (by omega) (by omega)).trans hm2,
    (k _ (by omega) (by omega)).trans hm3, a2, a3, a4, a5, a6⟩

/-- the stack header's capacity word survives a write to the window ranges `FWp` -/
theorem capW (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FWp sp)) : stCap M st = stCap s.mem st := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  exact hF.readLE _ _ (by simp only [FWp, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `makeslice(Word, n, c)` call of the prologue and its return run (`runM1` / `runMN`) → `KS` -/
theorem mkSeg {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {n c : Nat} (hc : c = makeCap xl) (hn : n ≤ c) (hxc : xl ≤ c)
    (hn1 : n = xl) (hbud : makeCost xl ≤ b)
    (KSc : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 pZ cZ : Nat),
      KS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 pZ cZ →
      stCap S.mem st = stCap s.mem st → b - makeCost xl ≤ b1 → ReachesRet (LibW.program.link impl) ret0 S Q)
    (T : State) (M : Memory) (hpc : T.rip = BitVec.ofNat 64 mkE) (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h0 : T.regs 0 = BitVec.ofNat 64 7233184) (h3 : T.regs 3 = BitVec.ofNat 64 n) (h1 : T.regs 1 = BitVec.ofNat 64 c)
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx : T.xmm 15 = s.xmm 15) (hdf : T.df = s.df)
    (hm : T.mem = M) (hF : MemFrame s.mem M (FWp sp)) (hrg : M.regions = s.mem.regions)
    (hra : M.readLE (sp - 8) 8 = if xl = 1 then mk1R else mk2R)
    (hsl : ESl M sp st bp r zp xp xl xc yp yl yc mp ml mc)
    (r68 : xl ≠ 1 → M.readLE (sp + 0x68) 8 = xl + 4) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hE := hP.1
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsp64 : sp < 2 ^ 64 := by omega
  have hw : WC R L K g sp st zp zc s.mem M L b (stLen s.mem st) := wc_init hP hF hrg
  have hc17 : c ≤ 2 ^ 17 := by rw [hc]; unfold makeCap; split <;> omega
  have hc0 : 0 < c := by rw [hc]; unfold makeCap; split <;> omega
  have hbs : blockSize (8 * c) true ≤ b := by
    have := blockSize_le_allocCost (8 * c) true
    have e : makeCost xl = allocCost (8 * c) := by rw [hc]; rfl
    omega
  have hacc0 : s.mem.accessible (sp - 8) 0x228 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  refine mkCall hmk hP hw hn hc0 hc17 hbs T hpc h4 h14 hm (by rw [hra]; split <;> decide) h0 h3 h1
    (fun ptr junk fl x yh m zh kr hA => ?_)
  obtain ⟨t4, t14, tfs, tx, tdf, tpc, tm⟩ := @rs_regs T junk [ptr] fl x yh m zh kr
  have ecap : stCap m st = stCap s.mem st := by
    obtain ⟨hstw, -⟩ := hP.stkF
    unfold Apart at hstw
    exact (hA.rdH (st + 16) 8 (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)).trans (capW hP hF)
  have kA : ∀ a k, sp + 24 ≤ a → a + k ≤ sp + 0x220 → m.readLE a k = M.readLE a k := fun a k h1 h2 =>
    hA.keep a k (Or.inr ⟨h1, h2⟩)
  have hsl' : ESl m sp st bp r zp xp xl xc yp yl yc mp ml mc :=
    hsl.keep (fun a k ha => kA a k (by simp only [SlotR] at ha; omega) (by simp only [SlotR] at ha; omega))
  have hacc : m.accessible (sp - 8) 0x228 true = true := by rw [hA.macc, hF.accessible]; exact hacc0
  have hrpc : (retState64 T junk [ptr] fl x yh m zh kr).rip =
      BitVec.ofNat 64 (if xl = 1 then mk1R else mk2R) := by
    rw [tpc, ra_eq (ra := if xl = 1 then mk1R else mk2R) h4 hsp64 (by rw [hm]; exact hra)]
  have hr4 : (retState64 T junk [ptr] fl x yh m zh kr).regs 4 = BitVec.ofNat 64 sp := by
    rw [t4, h4, bv_add8 (by omega) hsp64]
  have hc40 : c < 2 ^ 40 := by omega
  have hdl := dl_fresh hP hw hA hc40 hc0
  have hb' : b - makeCost xl ≤ b - blockSize (8 * c) true := by
    have := hA.rc
    have e : makeCost xl = allocCost (8 * c) := by rw [hc]; rfl
    omega
  have hjc : ∀ S3 : State, S3.regs 4 = BitVec.ofNat 64 sp → S3.regs 14 = T.regs 14 → S3.fsBase = T.fsBase →
      S3.xmm 15 = T.xmm 15 → S3.df = T.df → S3.mem = m →
      JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S3 (L ++ [(ptr.toNat, ptr.toNat +
        blockSize (8 * c) true)]) (b - blockSize (8 * c) true) := by
    intro S3 g4 g14 gfs gx gdf gm
    refine ⟨g4, g14.trans h14, ?_, gx.trans (hx.trans hE.2.2.2.1), gdf.trans (hdf.trans hE.2.2.2.2.1), ?_, ?_⟩
    · rw [gfs, hfs]; exact hE.2.2.1
    · rw [gm]; exact hA.wc
    · rw [gm]; exact hsl'
  have hptr : BitVec.ofNat 64 ptr.toNat = ptr := (bv_of_toNat (x := ptr) rfl).symm
  by_cases h1x : xl = 1
  · subst h1x
    have ec : c = 1 := by rw [hc]; rfl
    subst ec
    refine runM1 ret0 Q sp st xp 1 xc m hacc (by omega) hK5 hsl'.2.2.2.2.2.2.2.2.2.1
      hsl'.2.2.2.2.2.2.2.2.2.2.1 hsl'.2.2.2.2.2.2.2.2.2.2.2.1 hsl'.2.2.2.2.2.2.2.2.2.2.2.2 _ (by rw [hrpc]; rfl) hr4 tm ?_
    intro S3 epc e4 em e0 e1 e2 e8 e6 e7 e9 e14 efs ex edf
    refine KSc S3 _ _ ptr.toNat 1 ⟨hjc S3 e4 (e14.trans t14) (efs.trans tfs) (ex.trans tx) (edf.trans tdf) em, epc,
      by rw [em]; exact hdl, Nat.le_refl _, by rw [e0, rs_r0, hptr], e1, e2, e8, e6, e7, e9⟩  (by rw [em]; exact ecap) hb'
  · have ec : c = xl + 4 := by rw [hc]; unfold makeCap; rw [if_neg h1x]
    subst ec
    have hn' : n = xl := hn1
    refine runMN ret0 Q sp st xp xl xc m hacc (by omega) hK5 hsl'.2.2.2.2.2.2.2.2.2.1
      hsl'.2.2.2.2.2.2.2.2.2.2.1 hsl'.2.2.2.2.2.2.2.2.2.2.2.1 hsl'.2.2.2.2.2.2.2.2.2.2.2.2
      ((kA (sp + 0x68) 8 (by omega) (by omega)).trans (r68 h1x)) _ (by rw [hrpc, if_neg h1x]) hr4 tm ?_
    intro S3 epc e4 em e0 e1 e2 e8 e6 e7 e9 e14 efs ex edf
    refine KSc S3 _ _ ptr.toNat (xl + 4) ⟨hjc S3 e4 (e14.trans t14) (efs.trans tfs) (ex.trans tx) (edf.trans tdf) em,
      epc, by rw [em]; exact hdl, by omega, by rw [e0, rs_r0, hptr], e1, e2, e8, e6, e7, e9⟩  (by rw [em]; exact ecap) hb'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`segE`: entry → `KS`** (see the module doc) -/
theorem segE {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hxl0 : 0 < xl)
    (hbud : makeCost xl ≤ b) (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zc) (h7 : s.regs 7 = BitVec.ofNat 64 st)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl) (h9 : s.regs 9 = BitVec.ofNat 64 xc)
    {ret0 : W64} {Q : State → Prop}
    (KSc : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 pZ cZ : Nat),
      KS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 pZ cZ →
      stCap S.mem st = stCap s.mem st → b - makeCost xl ≤ b1 → ReachesRet (LibW.program.link impl) ret0 S Q) :
    ReachesRet (LibW.program.link impl) ret0 s Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hE := hP.1
  have hce := hP.cenv0
  obtain ⟨-, -, -, hwacc, hg1, hg2, hg3, -⟩ := hce
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxc : xc < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzp : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : st < 2 ^ 64 := by have := hP.stk0.2.2.2.1; omega
  obtain ⟨h5n, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h5 : s.regs 5 = BitVec.ofNat 64 bp := bv_of_toNat h5n
  have hbp : bp < 2 ^ 64 := by rw [← h5n]; exact (s.regs 5).isLt
  have hacc : s.mem.accessible (sp - 8) 0x228 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runE ret0 Q sp g zp zc st xp xl xc bp s.mem (by omega) hK5 hacc hg1 hg2 (by omega) hbp hzp hzc hxp
    (by omega) hxc hst s hpc hE.1 h0 h1 h7 h6 h8 h9 h5 hE.2.1 rfl ?_ ?_ ?_
  · intro S' M' pcS spS hle e0 e1 e2 e8 e6 e7 e9 e14 efs ex edf mS hF hrg a1 a2 a3 a4 a5 a6
    have hw : WC R L K g sp st zp zc s.mem M' L b (stLen s.mem st) := wc_init hP hF hrg
    subst mS
    refine KSc S' L b zp zc ⟨⟨spS, e14, by rw [efs]; exact hE.2.2.1, ex.trans hE.2.2.2.1, edf.trans hE.2.2.2.2.1,
      hw, esl_of hP hF a1 a2 a3 a4 a5 a6⟩, pcS, dl_reuse hP hF (by omega), hle, e0, e1, e2, e8, e6, e7, e9⟩
      (capW hP hF) (Nat.sub_le _ _)
  · intro S' M' pcS spS hlt h1x e0 e3 e1 e14 efs ex edf mS hF hrg rra a1 a2 a3 a4 a5 a6
    subst h1x
    exact mkSeg hmk hP (n := 1) (c := 1) rfl (Nat.le_refl _) (Nat.le_refl _) rfl hbud KSc S' M' pcS spS e0 e3 e1 e14 efs ex edf mS hF hrg
      (by rw [rra]; rfl) (esl_of hP hF a1 a2 a3 a4 a5 a6) (fun h => absurd rfl h)
  · intro S' M' pcS spS hlt h1x e0 e3 e1 e14 efs ex edf mS hF hrg rra a1 a2 a3 a4 a5 a6 a7
    exact mkSeg hmk hP (n := xl) (c := xl + 4) (by unfold makeCap; rw [if_neg h1x]) (by omega) (by omega) rfl hbud KSc S' M' pcS spS e0 e3 e1
      e14 efs ex edf mS hF hrg (by rw [rra, if_neg h1x]) (esl_of hP hF a1 a2 a3 a4 a5 a6) (fun _ => a7)

end

end FvModexp.Amd64.ExpSlow
