import FvModexp.Proofs.Amd64.Nat.BasicSqrDfr

/-!
# `basicSqr` (amd64): the postcondition at the return (pure)

From the loop's final memory `M` (`Inv … n M`), the memory `E` at the closure call (`t` doubled, `z += t`, frame stores)
and the memory `F` after the closure (`len(stk.w)` restored, closure frame): `Post`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.BasicSqr

/-- the ranges written between the loop exit and the closure call -/
@[reducible] def wsE (sp t zp zl xl : Nat) : List (Nat × Nat) :=
  [(t, t + 16 * xl), (zp, zp + 8 * zl), (sp - 200, sp - 112), (sp - 89, sp - 88), (sp - 56, sp - 48)]

/-- the ranges the closure writes -/
@[reducible] def wsF (sp st : Nat) : List (Nat × Nat) := [(sp - 208, sp - 192), (st + 8, st + 16)]

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
    ∀ r ∈ L1, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 64 ≤ r.1 := by
  obtain ⟨ns, hL1, hns, -⟩ := hE.ext
  have hout := hE.pre.ce.2.2.2.2.1
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
    Outside ((s.regs 14).toNat + 16) 8 (R.rt ++ win s 4424 64 ++ [(zp, zp + 8 * zl), (t, t + 16 * xl)] ++
      stkWs s.mem st) := by
  have hpre := hE.pre
  obtain ⟨-, -, -, -, -, hga, hgr, -, -, -⟩ := hpre.ce
  have hl := hE.lay
  have hzl := hl.zl2
  have hlc := hpre.stok.2.2.2.2.2.1
  have htg : Apart t (16 * xl) ((s.regs 14).toNat + 16) 8 := by
    rcases hE.scr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have ha := (hpre.starr h0).2; unfold Apart at ha ⊢; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have hzg := hpre.zg; have hstg := hpre.stg; have hfr := hpre.stgf
  simp only [freeP, freeN] at hfr
  unfold Apart at htg hzg hstg hga hfr
  simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨⟨hgr, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- the TLS slot `[fsBase - 8, fsBase)` is outside everything the function writes -/
theorem Env.tOut {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) :
    Outside (s.fsBase.toNat - 8) 8 (R.rt ++ win s 4424 64 ++ [(zp, zp + 8 * zl), (t, t + 16 * xl)] ++
      stkWs s.mem st) := by
  have hpre := hE.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨htb, -, -⟩, htrt, htw⟩ := hpre.ce
  have hl := hE.lay
  have hft := hl.ft; have hfz := hl.fz
  have hstt := hpre.stt; have hfr := hpre.stft
  simp only [freeP, freeN] at hfr
  unfold Apart at hstt hfr htw
  simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨⟨htrt, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega

set_option maxHeartbeats 1000000 in
theorem post_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl xc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) {M E F : Memory}
    (hI : Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 xl M)
    (hFE : MemFrame M E (wsE (s.regs 4).toNat t zp zl xl))
    (hz : natVal E zp zl = natVal s.mem xp xl * natVal s.mem xp xl)
    (hinvE : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 E))
    (hFF : MemFrame E F (wsF (s.regs 4).toNat st)) (hlen : F.readLE (st + 8) 8 = stLen s.mem st)
    (s' : State) (hs' : s'.mem = F) (hfs : s'.fsBase = s.fsBase) :
    Post R b L st zp zl xp xl s s' := by
  subst hs'
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0
  have hpre := hE.pre
  obtain ⟨-, -, -, -, hout, -, -, -, -, -⟩ := hpre.ce
  have hstok := hpre.stok
  obtain ⟨hst8, hsth, hstacc, hst48, -, hslc, -⟩ := hstok
  obtain ⟨hM, -, -, -⟩ := hI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m17, -, m19, -, -, mfr, mlf, minv⟩ := hM
  have hsw := hl.sw; have hsz := hl.sz; have hts := hl.ts; have htz := hl.tz; have hzw := hl.zw
  have hlsep := hl.lsep
  have hc1 := hE.c1len
  -- the whole frame
  have hMF := mfTrans (mfTrans mfr hFE) hFF
  have hacc : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hMF.accessible a n w
  have rdE : ∀ a n, Outside a n (wsE (s.regs 4).toNat t zp zl xl) → Outside a n (wsF (s.regs 4).toNat st) →
      s'.mem.readLE a n = M.readLE a n := fun a n h1 h2 => by rw [hFF.readLE a n h2, hFE.readLE a n h1]
  have hW : s'.mem.readLE st 8 = w1 := by
    rw [rdE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m17
  have hC : s'.mem.readLE (st + 16) 8 = c1 := by
    rw [rdE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m19
  have hzF : natVal s'.mem zp zl = natVal E zp zl :=
    hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨hfs, hzF.trans hz, L1, b1, hE.ext, hE.bud, ?inv, ?sb, ?mf, ?lf⟩
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
    simp only [win, ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨h1, h2⟩, h4, h5, h6⟩ := ho
    have ht := t_out hE h1 h6
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h4, ht⟩, h5, h6⟩, ht, h4, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals clear hlsep hsz hts htz hzw h4 h6 ht mlf mfr hMF; omega
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

abbrev callD : Nat := segAddr Extracted.program fn + 0x3c5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- from the closure call `CALL AX` (`stk.restore`) through the epilogue to the return -/
theorem fin4 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (M : Memory) (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat M)
    (E : State) (hpc : E.rip = BitVec.ofNat 64 callD) (hsp : E.regs 4 = s.regs 4 - 192#64)
    (h5 : E.regs 5 = s.regs 4 - 8#64) (h14 : E.regs 14 = s.regs 14) (hfs : E.fsBase = s.fsBase)
    (hx15 : E.xmm 15 = 0#128) (hdf : E.df = false)
    (r2 : E.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 40)) (r0 : E.regs 0 = 6232320#64)
    (hFE : MemFrame M E.mem (wsE (s.regs 4).toNat t zp.toNat zl.toNat xl.toNat))
    (hz : natVal E.mem zp.toNat zl.toNat = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat)
    (hinvE : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 E.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) E fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0
  have hpre := hE.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, -, -, -, -, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hstok := hpre.stok
  obtain ⟨hst8, hsth, hstacc, hst48, -, hslc, -⟩ := hstok
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, -, -, -, -, m7, m8, -, -, -, -, -, -, -, -, -, m18, -, -, mfr, -, -⟩ := hM
  have hsw := hl.sw; have hts := hl.ts; have hsz := hl.sz
  have hc1 := hE.c1len
  have rdE : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 200 ∨ (s.regs 4).toNat - 112 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 89 ∨ (s.regs 4).toNat - 88 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 56 ∨ (s.regs 4).toNat - 48 ≤ a) → (a + 8 ≤ t ∨ t + 16 * xl.toNat ≤ a) →
      (a + 8 ≤ zp.toNat ∨ zp.toNat + 8 * zl.toNat ≤ a) → E.mem.readLE a 8 = M.readLE a 8 :=
    fun a h1 h2 h3 h4 h5 => hFE.readLE _ _ (by simp only [wsE, outside_cons, outside_nil, and_true]; omega)
  have htw := hl.tw; have hzw := hl.zw
  have e1 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m1
  have e2 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m2
  have e7 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m7
  have e8 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m8
  have e18 := (rdE _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans m18
  have hEacc : ∀ a n w, E.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hFE.accessible, mfr.accessible]
  have hD := dsum impl
  have eD : segAddr LibBasicSqr.program fnD = 6232320 := by decide
  rw [eD] at hD
  have hstaccE : E.mem.accessible st.toNat 24 true = true := by rw [hEacc]; exact hstacc
  have hraccE : E.mem.accessible ((s.regs 4).toNat - 32) 16 false = true := by
    rw [hEacc]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  have hwaccE : E.mem.accessible ((s.regs 4).toNat - 208) 16 true = true := by
    rw [hEacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have f8 : E.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = st.toNat := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact e7
  have f16 : E.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 = stLen s.mem st.toNat := by
    rw [show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega]; exact e8
  have hra := hE.ra
  have hinvE' := hinvE
  clear hpre
  janus64_run [r2, r0, e1, e2, f8, f16, e18, mod64_of_lt ((s.regs 4).toNat - 40) (by omega)] calls [hD]
  janus_grab 200 as hFF
  have hlen : s'.mem.readLE (st.toNat + 8) 8 = stLen s.mem st.toNat := by assumption
  have hFF' : MemFrame E.mem s'.mem (wsF (s.regs 4).toNat st.toNat) :=
    MemFrame.trans (MemFrame.of_writeLE (rs := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192)]) E.mem 6232167
      (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)) hFF fun a n h => by
        simp only [wsF, outside_cons, outside_nil, and_true] at h ⊢; omega
  janus_grab hFF xmm 15 as hx'
  have hxx : s'.xmm 15 = s.xmm 15 := by rw [hx']; show E.xmm 15 = s.xmm 15; rw [hx15, hE.x15]
  have hfs2 : s'.fsBase = E.fsBase := by assumption
  refine ⟨⟨?_, ?_, ?_, hxx⟩, post_fin hE hI hFE hz hinvE hFF' hlen _ rfl (hfs2.trans hfs)⟩
  all_goals try janus64_simp
  all_goals first | exact hfs | skip

end FvModexp.Amd64.BasicSqr
