import FvModexp.Proofs.Amd64.Top.RunDJDefs

/-! # `Run` (amd64): operand 0, fresh `makeslice` buffer, `dst ≠ src` — the join `J0` to the `setBytes` call `pcE0`

At `J0` (`fn + 0x6a2`) the zeroed 32-byte stack buffer `e - 392` (`SI`) receives the `n = R10` available input bytes
from `src = BX` (`CMPQ SI, BX; JE` never taken: the input is outside the frame window), `memmove` returns at
`fn + 0x6ba`, the registers are reloaded, `e - 520 = min(h0, len - 96) + h1` is stored and the `setBytes` arguments
`buf = (DI, SI, R8) = (e - 392, h0, h0)`, `z = nil` are set up. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dJF0 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L0 : List (Nat × Nat)) (bk src dst e : Nat)
    (hj : JoinE R b L c p len cp s ret 0 L0 [(dst, e)] bk dst src S) (hfr : FreshDst R s (hdrV s p len 0) dst e)
    (hne0 : dst ≠ src)
    (hpc : S.rip = BitVec.ofNat 64 pcJ0)
    (hr6 : (S.regs 6).toNat = dst) (hr3 : (S.regs 3).toNat = src)
    (hr10 : (S.regs 10).toNat = min (hdrV s p len 0) (len.toNat - 96)) (hr1 : (S.regs 1).toNat = hdrV s p len 0)
    (hr2 : (S.regs 2).toNat = min (hdrV s p len 0) (len.toNat - 96)) (hr13 : (S.regs 13).toNat = hdrV s p len 1)
    (hk : ∀ S2, AtE R b L c p len cp s ret 0 pcE0 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hrel, hsl0, hzb, hsrc0, hsrc1, hsrc2, hd48, hdacc, hextL0, hsepb, -⟩ := hj
  obtain ⟨hfe, hfrt, hfw⟩ := hfr
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s3, s4, s5, s6, l0, l1, l2, lnz, -, hz,
    hdS, hinS, hcS, hext, hbk, hinv, hLsS, hMF, hLF, -, -⟩ := hrel
  have hsl := hsl0 rfl
  simp only [opLen, opAvail, opStart, stkBuf, ↓reduceIte, Nat.sub_zero, Nat.add_zero, Nat.mul_zero] at hzb hsrc1 hsrc2 hd48 hdacc
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz (by decide)
  obtain ⟨ho0, ho1, ho2, ho3⟩ := opAt_eqs (j := 0) hb' (by decide)
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero] at ho0 ho1 ho2 ho3
  simp only [opAt, Nat.mul_zero, Nat.sub_zero, ho1, ho2, ho3] at hz0 hz1 hz2 hz3
  rw [hx0] at hx15
  rw [hdf0] at hdf
  have hmv' : MemmoveLive64 (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmv
  have hLs0 := hLsS
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  obtain ⟨⟨hfs8, hfsacc, hfsg⟩, hfsrt, hfsw⟩ := htls
  unfold Apart at hfsw hga
  simp only [stk] at hfsw
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp]; exact toNat_sub_k (Nat.le_trans (by decide) hb') (by decide)
  simp only [LiveSep, win] at hLsS
  simp only [win, Outside, and_true] at hpw hcw
  have hLsL1 : LiveSep (L0 ++ [(dst, e)]) (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (win_len hb')
  have hstk : stk = 4800 := rfl
  -- the copy: `memmove(e - 392, src, n)`, `n = min(h0, len - 96) ≤ 32`
  have hnh : min (hdrV s p len 0) (len.toNat - 96) ≤ hdrV s p len 0 := Nat.min_le_left _ _
  have hd48' : dst + min (hdrV s p len 0) (len.toNat - 96) ≤ 2 ^ 48 := Nat.le_trans (Nat.add_le_add_left hnh _) hd48
  have hmvok : R.ok (cA "runtime.memmove") [dst, src, min (hdrV s p len 0) (len.toNat - 96)] :=
    hokM _ _ _ (Nat.le_trans hnh (Nat.le_trans l0 (by decide)))
  simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true] at hfw
  have hfw' : dst + min (hdrV s p len 0) (len.toNat - 96) ≤ (s.regs 4).toNat - 4800 ∨ (s.regs 4).toNat + 40 ≤ dst := by
    rcases hfw with h | h
    · exact Or.inl (Nat.le_trans (Nat.add_le_add_left hnh _) (Nat.le_trans hfe (by rw [Nat.add_sub_cancel' (Nat.le_trans (Nat.le_add_right _ _) hfe)] at h; exact h)))
    · exact Or.inr h
  obtain ⟨hdf1, hdf2, hdf3, hdf4⟩ := fresh_call_facts hb' hfw'
  have hsacc : s.mem.accessible src (min (hdrV s p len 0) (len.toNat - 96)) false = true :=
    Janus.Arm64.Memory.accessible_mono _ hpacc hsrc0 hsrc1
  have hSacc : S.mem.accessible src (min (hdrV s p len 0) (len.toNat - 96)) false = true := by
    rw [hMF.accessible]; exact hsacc
  have hsne : src ≠ dst := fun h => hne0 h.symm
  have hne : (S.regs 6 = S.regs 3) = False := bv_eq_false_of (by rw [hr6, hr3]; exact hsne.symm)
  have hne' : (S.regs 3 = S.regs 6) = False := bv_eq_false_of (by rw [hr6, hr3]; exact hsne)
  have hBuf : InRanges dst (min (hdrV s p len 0) (len.toNat - 96)) (L0 ++ [(dst, e)]) :=
    ⟨(dst, e), by simp, Nat.le_refl _, Nat.le_trans (Nat.add_le_add_left hnh _) hfe⟩
  have hLSd : Outside dst (e - dst)
      ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
          ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
        [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    rw [Nat.add_sub_cancel' (Nat.le_trans (Nat.le_add_right _ _) hfe)] at hfw ⊢
    omega
  have hLSm : ∀ r ∈ L0, Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
          ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
        [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
    intro r hr; have := hLsS r (List.mem_append_left _ hr)
    simp only [Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; omega
  have hdaccS : S.mem.accessible dst (min (hdrV s p len 0) (len.toNat - 96)) true = true := by
    rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hdacc (Nat.le_refl _) (Nat.add_le_add_left hnh _)
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hgr, win_apart_out hb' hga⟩)
  have hgA : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hMF.accessible]; exact hg2
  obtain ⟨hcf1, hcf2, hcf3, hcf4⟩ := frame_call_facts hal hg3 hga
  obtain ⟨hsf1, hsf2, hsf3⟩ := src_call_facts hb' hsrc0 hsrc1 hp hpw
  have bx2 := Box.mk hpw
  have bx := Box.mk <|
    And.intro hm2 <| And.intro hm3 <| And.intro hm4 <| And.intro hm5 <| And.intro hm6 <|
    And.intro l0 <| And.intro l1 <| And.intro l2 <| And.intro lnz <| And.intro hdS <| And.intro hinS <| And.intro
    hcS <| And.intro hext <| And.intro hbk <| And.intro hLsS <| And.intro hextL0 <| And.intro hsepb <| And.intro hfw <| And.intro hMF <| And.intro hLF <| And.intro hzb <|
    And.intro hsrc0 <| And.intro hsrc1 <| And.intro hsrc2 <| And.intro hd48 <| And.intro hdacc <| And.intro hLs0 <|
    And.intro hLsL1 <| And.intro hwrt <| And.intro hsacc <| And.intro hcacc <| And.intro hc48 <| And.intro hcheld
    <| And.intro hp <| And.intro hlcp <| And.intro hcp48 <| And.intro hpacc <| And.intro hheld <|
    And.intro hd <| And.intro hro <| And.intro hLs <| And.intro
    hgr <| And.intro hfs8 <| And.intro hfsacc <| And.intro hfsg hfsrt
  clear hm2 hm3 hm4 hm5 hm6 l0 l1 l2 lnz hdS hinS hcS hext hbk hLsS hextL0 hsepb hfw hMF hLF hzb hsrc0 hsrc1 hsrc2 hd48 hdacc hLs0 hLsL1
    hwrt hsacc hcacc hc48 hcheld hcw hp hlcp hcp48 hpacc hheld hpw hd hro hLs hgr hfs8 hfsacc hfsg hfsrt hfsw
    hokM hsl0 hz hmv
  set_option janus.callRegions true in
  janus64_run [hr6, hr3, hr10, hr1, hr2, hr13, hne, hne', hm1, hgS, s1, s2, s3, s4, s5, s6, hsl, hz0, hz1, hz2, hz3, hx15,
    hdf, toInt_ite, toNat_ite, BitVec.msb_eq_decide] until [pcE0] calls [hmv']
  rename_i _ _ _ _ m _ _ hMFv hLFv hinvv hcp
  obtain ⟨hm2, hm3, hm4, hm5, hm6, l0, l1, l2, lnz, hdS, hinS, hcS, hext, hbk, hLsS, hextL0, hsepb, hfw, hMF, hLF, hzb, hsrc0, hsrc1, hsrc2,
    hd48, hdacc, hLs0, hLsL1, hwrt, hsacc, hcacc, hc48, hcheld, hp, hlcp, hcp48, hpacc, hheld, hd, hro, hLs, hgr,
    hfs8, hfsacc, hfsg, hfsrt⟩ := bx.h
  clear hsf2 hsf3 hcf3 hcf4 hga hdf1 hdf2 hdf3
  have hMFm : MemFrame S.mem m (R.rt ++ win s stk 40) := by simp only [win, stk]; janus_frame
  have hd1 := dataLoaded_frame64 hdS (by simp [hrg1]) hro hMFm (fun r hr _ => by
    simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact Janus.Arm64.Memory.accessible_mono _ hwS (Nat.le_refl _) (win_len hb'))
  clear hdS
  have hdst : LiveSep L0 [(dst, dst + min (hdrV s p len 0) (len.toNat - 96))] :=
    liveSep_single_sub hsepb (Nat.le_trans (Nat.add_le_add_left hnh _) hfe)
  have hLsL0 : LiveSep L0 (win s 4800 40) := fun r hr => hLsL1 r (List.mem_append_left _ hr)
  have hLFS : LiveFrame S.mem m L0 [] :=
    ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL0).trans
      (LiveFrame.drop (L := L0) ⟨fun a n h hw => hLFv.readLE a n (h.append_left _) hw⟩ hdst) (fun _ _ h => h))
  refine hk _ ⟨L0 ++ [(dst, e)], bk, RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz ?_ ?_ ?_ hext ?_
    ?_ hLs0 ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ h => absurd h (Nat.not_lt_zero _)), by janus64_simp,
    by janus64_simp, by janus64_simp, by janus64_simp, ?buf⟩
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf.trans hdf0.symm; done) | (simp only [hfs]; done) | (simp only [hdf, hdf0]; done))
  case refine_19 =>
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
    · janus64_simp
    · janus64_simp
  case refine_20 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt, Nat.mul_zero, Nat.sub_zero, ho1, ho2, ho3]
    all_goals janus64_simp [hz0, hz1, hz2, hz3]
  case refine_21 => janus64_callpre
  case refine_22 => simp only [cstD, cstE] at hbk ⊢; exact hbk
  case refine_23 =>
    dsimp only
    rw [view_writeLE_out (hout.of_sub (buf_in_win (k := 520) (n := 8) hb' (by decide) (by decide)).1
      (buf_in_win (k := 520) (n := 8) hb' (by decide) (by decide)).2)]
    first | exact hinvv | exact RtInv.inv_congr hinvv rfl (by janus64_simp) rfl
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact (hLF.trans hLFS (fun _ _ h => hextL0.inRanges_old h)).trans
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL0) (fun _ _ h => hextL0.inRanges_old h)
  case buf =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try janus64_simp
    · simp only [opLen, ↓reduceIte]
    · have hpw := bx2.h
      simp only [opV, opStart, opLen, ↓reduceIte, Nat.add_zero]
      rw [beVal_writeLE_disj (fresh_slot hb' (by decide) (by decide) hfw
        (by have := Nat.le_trans (Nat.le_add_right _ _) hfe; omega))]
      refine padded_val hcp ?_ ?_ rfl
      · intro hn i hi
        rw [hsrc2 hn]
        obtain ⟨r1, r2⟩ := in_rng (p := p.toNat) (st := 0) (by simpa using hi)
        simp only [Nat.add_zero] at r1 r2
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (in_byte_out hb' (by decide) (by decide) r1 r2 hpw),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (in_byte_out hb' (by decide) (by decide) r1 r2 hpw),
          hinS _ _ r1 r2, Nat.add_assoc]
      · intro i h1 h2
        rw [hLFv.readLE _ _ ⟨(dst, e), by simp, Nat.le_add_right _ _, Nat.le_trans (Nat.add_le_add_left (Nat.succ_le_of_lt h2) dst) hfe⟩ (by
          simp only [Janus.outside_cons, Janus.outside_nil, and_true]; exact Or.inr (Nat.add_le_add_left h1 _))]
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (fresh_byte_out hb' (by decide) (by decide) hfw (lt_sub_of_add h2 hfe)),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (fresh_byte_out hb' (by decide) (by decide) hfw (lt_sub_of_add h2 hfe))]
        exact hzb i h2
    · exact Janus.Arm64.Memory.accessible_read_of_write _ hdacc
    · exact hd48
    · exact Or.inl ⟨(dst, e), by simp, Nat.le_refl _, hfe⟩
    · exact (fresh_call_facts (n := hdrV s p len 0) hb' (by
        rcases hfw with h | h
        · exact Or.inl (Nat.le_trans hfe (by rw [Nat.add_sub_cancel' (Nat.le_trans (Nat.le_add_right _ _) hfe)] at h; exact h))
        · exact Or.inr h)).2.2.2

end FvModexp.Amd64.Run
