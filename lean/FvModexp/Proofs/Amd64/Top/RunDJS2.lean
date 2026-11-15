import FvModexp.Proofs.Amd64.Top.RunDJDefs
import FvModexp.Proofs.Amd64.Top.RunDSlot

/-! # `Run` (amd64): operand 2, stack buffer — the join `J1` to the `setBytes` call `pcE2`

At `J2` (`fn + 0x9c7`) the zeroed 32-byte stack buffer `e - 456` (`AX`) receives the `n = DX` available input bytes
from `src = BX` (`CMPQ AX, BX; JE` never taken: the input is outside the frame window), `memmove` returns at
`fn + 0x9dc`, the registers are reloaded, the `setBytes` arguments
`buf = (DI, SI, R8) = (e - 456, h2, h2)`, `z = nil` are set up. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dJS2 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L0 : List (Nat × Nat)) (bk src : Nat)
    (hj : JoinE R b L c p len cp s ret 2 L0 [] bk (stkBuf s 2) src S) (hsz : hdrV s p len 2 ≤ 32)
    (hpc : S.rip = BitVec.ofNat 64 pcJ2)
    (hr6 : (S.regs 0).toNat = (s.regs 4).toNat - 456) (hr3 : (S.regs 3).toNat = src)
    (hr10 : (S.regs 2).toNat = opAvail s p len 2) (hr1 : (S.regs 1).toNat = hdrV s p len 2)
    (hk : ∀ S2, AtE R b L c p len cp s ret 2 pcE2 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hrel, -, hzb, hsrc0, hsrc1, hsrc2, hd48, hdacc, -, -, hop0⟩ := hj
  rw [List.append_nil] at hrel
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s3, s4, s5, s6, l0, l1, l2, lnz, hslD, hz,
    hdS, hinS, hcS, hext, hbk, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  obtain ⟨hsl, hsl2⟩ := hslD.1 (by decide)
  have hsl3 := hslD.2 (Nat.le_refl _)
  have hoL : opLen s p len 2 = hdrV s p len 2 := rfl
  have hoA : opAvail s p len 2 = min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1)) := rfl
  have hoS : opStart s p len 2 = hdrV s p len 0 + hdrV s p len 1 := rfl
  simp only [hoL, hoA, hoS, stkBuf] at hzb hsrc1 hsrc2 hd48 hdacc hr10
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz (by decide)
  simp only [opAt] at hz0 hz1 hz2 hz3
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
  have hz1' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 192) 8 = 0 := by
    rw [show (s.regs 4).toNat - 192 = (s.regs 4).toNat - 136 - 32 * 2 + 8 by omega]; exact hz1
  have hz2' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 184) 8 = 0 := by
    rw [show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 136 - 32 * 2 + 16 by omega]; exact hz2
  have hz3' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 176) 8 = 0 := by
    rw [show (s.regs 4).toNat - 176 = (s.regs 4).toNat - 136 - 32 * 2 + 24 by omega]; exact hz3
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp]; exact toNat_sub_k (Nat.le_trans (by decide) hb') (by decide)
  simp only [LiveSep, win] at hLsS
  simp only [win, Outside, and_true] at hpw hcw
  have hLsL1 : LiveSep L0 (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (win_len hb')
  have hstk : stk = 4800 := rfl
  -- the copy: `memmove(e - 456, src, n)`, `n = min(h1, len - 96 - h0) ≤ 32`
  have hn32 : min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1)) ≤ 32 := Nat.le_trans (Nat.min_le_left _ _) hsz
  have hmvok : R.ok (cA "runtime.memmove") [(s.regs 4).toNat - 456, src, min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1))] :=
    hokM _ _ _ (Nat.le_trans hn32 (by decide))
  have hsacc : s.mem.accessible src (min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1))) false = true :=
    Janus.Arm64.Memory.accessible_mono _ hpacc hsrc0 hsrc1
  have hSacc : S.mem.accessible src (min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1))) false = true := by
    rw [hMF.accessible]; exact hsacc
  have hsne : src ≠ (s.regs 4).toNat - 456 :=
    src_ne_frame hsrc0 hsrc1 hpw hb' (by decide) (by decide)
  have hne : (S.regs 0 = S.regs 3) = False := bv_eq_false_of (by rw [hr6, hr3]; exact hsne.symm)
  have hne' : (S.regs 3 = S.regs 0) = False := bv_eq_false_of (by rw [hr6, hr3]; exact hsne)
  have hBuf : Outside ((s.regs 4).toNat - 456) (min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1))) R.rt :=
    hout.of_sub (buf_in_win hb' (by decide) (Nat.le_trans hn32 (by decide))).1
      (buf_in_win hb' (by decide) (Nat.le_trans hn32 (by decide))).2
  have hLSm : ∀ r ∈ L0, Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
          ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
        [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
    intro r hr; have := hLsS r hr
    simp only [Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; omega
  have hdaccS : S.mem.accessible ((s.regs 4).toNat - 456) (min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1))) true = true := by
    rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw
      (buf_in_win hb' (by decide) (Nat.le_trans hn32 (by decide))).1
      (buf_in_win hb' (by decide) (Nat.le_trans hn32 (by decide))).2
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
    hcS <| And.intro hext <| And.intro hbk <| And.intro hop <| And.intro hopA <| And.intro hop0 <| And.intro hsl2 <| And.intro hLsS <| And.intro hMF <| And.intro hLF <| And.intro hzb <|
    And.intro hsrc0 <| And.intro hsrc1 <| And.intro hsrc2 <| And.intro hd48 <| And.intro hdacc <| And.intro hLs0 <|
    And.intro hLsL1 <| And.intro hwrt <| And.intro hsacc <| And.intro hcacc <| And.intro hc48 <| And.intro hcheld
    <| And.intro hp <| And.intro hlcp <| And.intro hcp48 <| And.intro hpacc <| And.intro hheld <|
    And.intro hd <| And.intro hro <| And.intro hLs <| And.intro
    hgr <| And.intro hfs8 <| And.intro hfsacc <| And.intro hfsg hfsrt
  clear hm2 hm3 hm4 hm5 hm6 l0 l1 l2 lnz hdS hinS hcS hext hbk hop hopA hop0 hsl2 hLsS hMF hLF hzb hsrc0 hsrc1 hsrc2 hd48 hdacc hLs0 hLsL1
    hwrt hsacc hcacc hc48 hcheld hcw hp hlcp hcp48 hpacc hheld hpw hd hro hLs hgr hfs8 hfsacc hfsg hfsrt hfsw
    hokM hz hmv
  set_option janus.callRegions true in
  janus64_run [hr6, hr3, hr10, hr1, hne, hne', hm1, hgS, s1, s2, s3, s4, s5, s6, hsl, hz1', hz2', hz3', hx15,
    hdf, toInt_ite, toNat_ite, BitVec.msb_eq_decide] until [pcE2] calls [hmv']
  rename_i _ _ _ _ m _ _ hMFv hLFv hinvv hcp
  obtain ⟨hm2, hm3, hm4, hm5, hm6, l0, l1, l2, lnz, hdS, hinS, hcS, hext, hbk, hop, hopA, hop0, hsl2, hLsS, hMF, hLF, hzb, hsrc0, hsrc1, hsrc2,
    hd48, hdacc, hLs0, hLsL1, hwrt, hsacc, hcacc, hc48, hcheld, hp, hlcp, hcp48, hpacc, hheld, hd, hro, hLs, hgr,
    hfs8, hfsacc, hfsg, hfsrt⟩ := bx.h
  clear hsf2 hsf3 hcf3 hcf4 hga
  have hMFm : MemFrame S.mem m (R.rt ++ win s stk 40) := by simp only [win, stk]; janus_frame
  have hd1 := dataLoaded_frame64 hdS (by simp [hrg1]) hro hMFm (fun r hr _ => by
    simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact Janus.Arm64.Memory.accessible_mono _ hwS (Nat.le_refl _) (win_len hb'))
  clear hdS
  have hdst : LiveSep L0 [((s.regs 4).toNat - 456, (s.regs 4).toNat - 456 + min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1)))] := by
    intro r hr; have := hLsS r hr
    simp only [Outside, and_true] at this ⊢
    exact win_out_buf hb' (by decide) (Nat.le_trans hn32 (by decide)) this
  have hLFS : LiveFrame S.mem m L0 [] :=
    ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.drop hLFv hdst)
      (fun _ _ h => h))
  refine hk _ ⟨L0, bk, RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz ?_ ?_ ?_ hext ?_
    ?_ hLs0 ?_ ?_ ?_ ?_, by janus64_simp,
    by janus64_simp, by janus64_simp, by janus64_simp, ?buf⟩
  case refine_19 =>
    refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩
    · janus64_simp
    · janus64_simp [hsl2]
    · janus64_simp [hsl3]
  case refine_20 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt]
    all_goals janus64_simp [hz0, hz1, hz2, hz3]
  case refine_21 => janus64_callpre
  case refine_22 => simp only [cstD, cstE] at hbk ⊢; exact hbk
  case refine_23 =>
    dsimp only
    try rw [view_writeLE_out (hout.of_sub (buf_in_win (k := 552) (n := 8) hb' (by decide) (by decide)).1
      (buf_in_win (k := 552) (n := 8) hb' (by decide) (by decide)).2)]
    first | exact hinvv | exact RtInv.inv_congr hinvv rfl (by janus64_simp) rfl
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact (hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)).trans
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => hext.inRanges_old h)
  case refine_26 =>
    intro j hj
    refine OpDone.transportS (hop _ (by omega)) (k := 2) (by omega) ?_
      (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => h)) (fun _ _ h => h)
    intro a n h1 h2; simp only [opAt] at h1 h2; janus64_simp
  case refine_27 =>
    refine OpsApart.transportS hopA ?_
    intro a n h1 h2; simp only [opAt] at h1 h2; janus64_simp
  case buf =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try janus64_simp
    · rfl
    · have hpw := bx2.h
      simp only [opV, hoS, hoL]
      try rw [beVal_writeLE_disj (Or.inr (slot_lt hb' (by decide) (by decide)))]
      refine padded_val hcp ?_ ?_ (by omega)
      · intro hn i hi
        rw [hsrc2 hn]
        obtain ⟨r1, r2⟩ := in_rng (p := p.toNat) (st := hdrV s p len 0 + hdrV s p len 1) hi
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (in_byte_out hb' (by decide) (by decide) r1 r2 hpw),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (in_byte_out hb' (by decide) (by decide) r1 r2 hpw),
          hinS _ _ r1 r2, show p.toNat + 96 + (hdrV s p len 0 + hdrV s p len 1) + i = p.toNat + (96 + (hdrV s p len 0 + hdrV s p len 1) + i) by omega]
      · intro i h1 h2
        obtain ⟨b1, b2, b3, b4, b6⟩ := buf_byte (k := 456) (i := i) hb' (by decide) (by decide) (by omega)
        rw [hMFv.readLE _ _ (by
          simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
          exact ⟨⟨hout.of_sub b1 b2, b3, b4⟩, Or.inr (Nat.add_le_add_left h1 _)⟩)]
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ b6,
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (buf_byte_w hb' (by decide) (by decide) (by omega)
            (by decide) (by decide))]
        exact hzb i h2
    · exact Janus.Arm64.Memory.accessible_read_of_write _ hdacc
    · exact hd48
    · exact Or.inr (hout.of_sub (buf_in_win (k := 456) hb' (by decide) (Nat.le_trans hsz (by decide))).1
        (buf_in_win (k := 456) hb' (by decide) (Nat.le_trans hsz (by decide))).2)
    · exact Or.inr (cw_le hb' (by decide))
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf.trans hdf0.symm; done) | (simp only [hfs]; done) | (simp only [hdf, hdf0]; done))

end FvModexp.Amd64.Run
