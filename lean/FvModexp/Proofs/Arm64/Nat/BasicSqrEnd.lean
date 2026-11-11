import FvModexp.Proofs.Arm64.Nat.BasicSqrDfr

/-!
# `basicSqr` (arm64): the postcondition at the return (pure)

From the loop's final memory `M` (`Inv … n M`), the memory `E` at the closure call (`t` doubled, `z += t`, frame stores)
and the memory `F` after the closure (`len(stk.w)` restored, closure frame): `Post`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.BasicSqr

/-- the ranges written between the loop exit and the closure call -/
@[reducible] def wsE (sp t zp zl xl : Nat) : List (Nat × Nat) :=
  [(t, t + 16 * xl), (zp, zp + 8 * zl), (sp - 200, sp - 120), (sp - 89, sp - 88), (sp - 56, sp - 48)]

/-- the ranges the closure writes -/
@[reducible] def wsF (sp st : Nat) : List (Nat × Nat) := [(sp - 232, sp - 216), (st + 8, st + 16)]

theorem mfTrans {m₀ m₁ m₂ : Memory} {rs rs' : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs)
    (h₂ : MemFrame m₁ m₂ rs') : MemFrame m₀ m₂ (rs ++ rs') where
  readLE a k ho := by
    rw [outside_append] at ho
    rw [h₂.readLE a k ho.2, h₁.readLE a k ho.1]
  accessible a k w := by rw [h₂.accessible, h₁.accessible]

/-- `t` (in the stack's old free part or a fresh runtime block) is outside every range a caller keeps -/
theorem t_out {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1)
    {a n : Nat} (h1 : Outside a n R.rt)
    (h2 : a + n ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a) :
    a + n ≤ t ∨ t + 16 * xl ≤ a := by
  rcases hE.scr.loc with ⟨-, h3, h4⟩ | ⟨⟨r, hr, h3, h4⟩, -⟩
  · omega
  · have := MemFrame.outside_mem h1 hr; omega

theorem t_live {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1)
    {a n : Nat} (h1 : InRanges a n L)
    (h2 : a + n ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a) :
    a + n ≤ t ∨ t + 16 * xl ≤ a := by
  rcases hE.scr.loc with ⟨-, h3, h4⟩ | ⟨-, hap⟩
  · omega
  · have := hap.apart_of_inRanges h1; omega

/-- the live set after `stk.nat` keeps clear of the window -/
theorem Env.lsep1 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) :
    ∀ r ∈ L1, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ r.1 := by
  obtain ⟨ns, hL1, hns, -⟩ := hE.ext
  have hout := hE.pre.ce.2.2.2.1
  intro r hr
  rw [hL1] at hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hE.lay.lsep r hr
  · obtain ⟨⟨q, hq, h1, h2⟩, -⟩ := hns r hr
    have := MemFrame.outside_mem hout hq
    omega

/-- the stack-guard word is outside everything the function writes -/
theorem Env.gOut {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) :
    Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ winA s 4432 64 ++ [(zp, zp + 8 * zl), (t, t + 16 * xl)] ++
      stkWs s.mem st) := by
  have hpre := hE.pre
  obtain ⟨-, -, -, -, hga, hgr, -, -⟩ := hpre.ce
  have hl := hE.lay
  have hzl := hl.zl2
  have hlc := hpre.stok.2.2.2.2.2.1
  have htg : Apart t (16 * xl) ((s.regs 28).toNat + 16) 8 := by
    rcases hE.scr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have ha := (hpre.starr h0).2; unfold Apart at ha ⊢; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have hzg := hpre.zg; have hstg := hpre.stg; have hfr := hpre.stgf
  simp only [freeP, freeN] at hfr
  unfold Apart at htg hzg hstg hga hfr
  simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨⟨hgr, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega

set_option maxHeartbeats 1000000 in
theorem post_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl xc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) {M E F : Memory}
    (hI : Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 xl M)
    (hFE : MemFrame M E (wsE s.sp.toNat t zp zl xl))
    (hz : natVal E zp zl = natVal s.mem xp xl * natVal s.mem xp xl)
    (hinvE : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 E))
    (hFF : MemFrame E F (wsF s.sp.toNat st)) (hlen : F.readLE (st + 8) 8 = stLen s.mem st)
    (s' : State) (hs' : s'.mem = F) :
    Post R b L st zp zl xp xl s s' := by
  subst hs'
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0
  have hpre := hE.pre
  obtain ⟨-, -, -, hout, -, -, -, -⟩ := hpre.ce
  have hstok := hpre.stok
  obtain ⟨hst8, hsth, hstacc, hst48, -, hslc, -⟩ := hstok
  obtain ⟨hM, -, -, -⟩ := hI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m17, -, m19, -, mfr, mlf, minv⟩ := hM
  have hsw := hl.sw; have hsz := hl.sz; have hts := hl.ts; have htz := hl.tz; have hzw := hl.zw
  have hlsep := hl.lsep
  have hc1 := hE.c1len
  -- the whole frame
  have hMF := mfTrans (mfTrans mfr hFE) hFF
  have hacc : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hMF.accessible a n w
  have rdE : ∀ a n, Outside a n (wsE s.sp.toNat t zp zl xl) → Outside a n (wsF s.sp.toNat st) →
      s'.mem.readLE a n = M.readLE a n := fun a n h1 h2 => by rw [hFF.readLE a n h2, hFE.readLE a n h1]
  have hW : s'.mem.readLE st 8 = w1 := by
    rw [rdE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m17
  have hC : s'.mem.readLE (st + 16) 8 = c1 := by
    rw [rdE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m19
  have hzF : natVal s'.mem zp zl = natVal E zp zl :=
    hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨hzF.trans hz, L1, b1, hE.ext, hE.bud, ?inv, ?sb, ?mf, ?lf⟩
  case inv =>
    refine RtInv.inv_frame' hFF (fun r hr => ?_) hinvE
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · left; exact hout.of_sub (by omega) (by omega)
    · have := (hE.ext.held hsth).sub (a := st + 8) (n := 8) (by omega) (by omega)
      rcases this with h | h
      · right; simpa using h
      · left; simpa using h
  case sb =>
    refine ⟨⟨hst8, hE.ext.held hsth, by rw [hacc]; exact hstacc, hst48, ?_, ?_, ?_⟩, hlen, ?_⟩
    · show NatLive s'.mem R L1 (s'.mem.readLE st 8) (s'.mem.readLE (st + 16) 8)
      rw [hW, hC]
      intro h0
      obtain ⟨a1, a2, a3, a4⟩ := hE.w1live h0
      exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
    · show s'.mem.readLE (st + 8) 8 ≤ s'.mem.readLE (st + 16) 8
      rw [hlen, hC]; omega
    · show s'.mem.readLE (st + 16) 8 < 2 ^ 40
      rw [hC]; exact hE.c1b
    · show (s'.mem.readLE st 8 = stW s.mem st ∧ s'.mem.readLE (st + 16) 8 = stCap s.mem st) ∨
        (InRanges (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) R.rt ∧
          ApartAll (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) L)
      rw [hW, hC]; exact hE.arr
  case mf =>
    refine hMF.mono fun a n ho => ?_
    simp only [winA, ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := ho
    have ht := t_out hE h1 h6
    refine ⟨⟨⟨⟨⟨h1, h2, h3⟩, h4, ht⟩, h5, h6⟩, ht, h4, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals clear hlsep hsz hts htz hzw h3 h4 h6 ht mlf mfr hMF; omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    simp only [ws, stkWs, outside_cons, outside_nil, and_true] at ho
    obtain ⟨h4, h5, h6⟩ := ho
    have ht := t_live hE hin h6
    obtain ⟨r, hr, i1, i2⟩ := hin
    have hr' := hlsep r hr
    rw [rdE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact mlf.readLE a n ⟨r, hr, i1, i2⟩
      (by simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]; omega)

abbrev callD : Nat := segAddr Extracted.program fn + 0x26c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
/-- from the closure call `CALL (R0)` (`stk.restore`) through the epilogue to the return -/
theorem fin4 (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (M : Memory) (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat M)
    (E : State) (hpc : E.pc = BitVec.ofNat 64 callD) (hsp : E.sp = s.sp - 208#64) (h28 : E.regs 28 = s.regs 28)
    (h29 : E.regs 29 = s.sp - 216#64) (h18 : E.regs 18 = s.regs 18)
    (r26 : E.regs 26 = BitVec.ofNat 64 (s.sp.toNat - 40)) (r0 : E.regs 0 = 1817392#64)
    (hFE : MemFrame M E.mem (wsE s.sp.toNat t zp.toNat zl.toNat xl.toNat))
    (hz : natVal E.mem zp.toNat zl.toNat = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat)
    (hinvE : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 E.mem))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) E fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hret, hout, hga, hgr, -, -⟩ := hpre.ce
  have hstok := hpre.stok
  obtain ⟨hst8, hsth, hstacc, hst48, -, hslc, -⟩ := hstok
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, -, -, -, -, -, m8, m9, -, -, -, -, -, -, -, -, -, m19, -, mfr, -, -⟩ := hM
  have hsw := hl.sw; have hts := hl.ts; have hsz := hl.sz
  have hc1 := hE.c1len
  have rdE : ∀ a, (a + 8 ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 120 ≤ a) → (a + 8 ≤ s.sp.toNat - 89 ∨ s.sp.toNat - 88 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 48 ≤ a) → (a + 8 ≤ t ∨ t + 16 * xl.toNat ≤ a) →
      (a + 8 ≤ zp.toNat ∨ zp.toNat + 8 * zl.toNat ≤ a) → E.mem.readLE a 8 = M.readLE a 8 :=
    fun a h1 h2 h3 h4 h5 => hFE.readLE _ _ (by simp only [wsE, outside_cons, outside_nil, and_true]; omega)
  have htw := hl.tw; have hzw := hl.zw
  have e1 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m1
  have e2 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m2
  have e8 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m8
  have e9 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m9
  have e19 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m19
  have eg : E.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    have htg : Apart t (16 * xl.toNat) ((s.regs 28).toNat + 16) 8 := by
      rcases hE.scr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
      · have ha := (hpre.starr h0).2; have := hpre.stok.2.2.2.2.2.1; unfold Apart at ha ⊢; omega
      · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
    have hzg := hpre.zg; have hstg := hpre.stg
    have hlc := hpre.stok.2.2.2.2.2.1
    have hfr : Apart (stW s.mem st.toNat + 8 * stLen s.mem st.toNat) (8 * (stCap s.mem st.toNat - stLen s.mem st.toNat))
          ((s.regs 28).toNat + 16) 8 := hpre.stgf
    unfold Apart at htg hzg hstg hga hfr
    rw [hFE.readLE _ _ (by simp only [wsE, outside_cons, outside_nil, and_true]; omega),
      mfr.readLE _ _ (by
        simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true]
        refine ⟨⟨⟨hgr, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega)]
  have hEacc : ∀ a n w, E.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hFE.accessible, mfr.accessible]
  have hD := dsum impl
  have eD : segAddr LibBasicSqr.program fnD = 1817392 := by decide
  rw [eD] at hD
  clear hpre
  have f8 : M.readLE (s.sp.toNat - 40 + 8) 8 = st.toNat := by
    rw [show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact m8
  have f16 : M.readLE (s.sp.toNat - 40 + 16) 8 = stLen s.mem st.toNat := by
    rw [show s.sp.toNat - 40 + 16 = s.sp.toNat - 24 by omega]; exact m9
  janus_run [e1, e2, e8, e9, e19, eg, f8, f16] calls [hD]
  rename_i hlen hFF _
  rw [show s.sp.toNat - 208 - 24 = s.sp.toNat - 232 by omega, show s.sp.toNat - 208 - 8 = s.sp.toNat - 216 by omega]
    at hFF
  exact post_fin hE hI hFE hz hinvE hFF hlen _ rfl

end FvModexp.Arm64.BasicSqr
