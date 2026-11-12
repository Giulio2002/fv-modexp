import FvModexp.Proofs.Amd64.Top.RunHMask
import FvModexp.Proofs.Amd64.Top.RunSmall
import FvModexp.Proofs.Amd64.Top.RunBox

/-! # `Run` (amd64): `B2` to `B3`, `64 ≤ len < 96` (header 2 = `modLen`: `getData(input, 64, 32)`, std `setBytes`)

amd64 code (`fn = 0x654340`): `B1 = 0x654470` zeroes the header `big.Int` at `e - 72`; `getData`: `CX = min(len, end)`,
`R9 = start` (slots `e - 504`, `e - 496`), `JA` slice panic (refuted), size `CX - R9`, re-slice mask
`(-(cap - start)) >> 63 & start` (`neg_asr63_and`); size `< 32` → buffer `e - 360` zeroed by two `MOVUPS X15` stores,
`memmove(buf, src, size)` (the `CMPQ AX, BX; JE` skip refuted: the input is outside the window), join `0x654530`,
`setBytes` (return `0x65467a`), stores, `B2 = 0x65457c`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts


namespace FvModexp.Amd64.Run

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem h3m (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hokr : HdrOkR R b len)
    (Q : Janus.Amd64.Outcome → Prop)
    (hk : ∀ S L2 b2, RelH R b L c p len cp s ret 3 L2 b2 S → S.rip = BitVec.ofNat 64 pcB3 →
      (S.regs 0).toNat = S.mem.readLE ((s.regs 4).toNat - 96) 8 → (S.regs 3).toNat = S.mem.readLE ((s.regs 4).toNat - 88) 8 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 2 L1 b1 S)
    (hpc : S.rip = BitVec.ofNat 64 pcB2) (h64 : 64 ≤ len.toNat) (h96 : len.toNat < 96) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hok, hcost, hokm⟩ := hokr
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, hsl, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF,
    hLF, hhd⟩ := hrel
  obtain ⟨hsl1, hsl2⟩ := hsl (by omega)
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
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hgr, by omega⟩)
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 :=
    hMF.readLE _ _ (by
      simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hfsrt, by omega⟩)
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  simp only [LiveSep, win] at hLsS
  simp only [win, Outside, and_true] at hpw hcw
  have hS := RunCallees.sbStdD impl hap R hmk b1 L1
  have hwT : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwT hok
  have hLS1 : ∀ r ∈ L1, r.fst + (r.snd - r.fst) ≤ BitVec.toNat (s.regs 4) - 616 - 4160 ∨
      BitVec.toNat (s.regs 4) - 616 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hBuf : InRanges (BitVec.toNat (s.regs 4) - 360) 32 L1 ∨ Outside (BitVec.toNat (s.regs 4) - 360) 32 R.rt :=
    Or.inr (hout.of_sub (by omega) (by omega))
  have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by omega)
  have hstk : stk = 4800 := rfl
  have hspn' : (s.regs 4 - 616#64).toNat = (s.regs 4).toNat - 616 := by rw [BitVec.toNat_sub]; simp; omega
  have hcp63 : cp.toNat < 2 ^ 63 := by omega
  have hmin : min len.toNat 32 = 32 := by omega
  have hc : (len.toNat < 64) = False := by simp; omega
  have hc96 : (len.toNat < 96) = True := by simp; omega
  have h3263 : (64#64).toNat < 2 ^ 63 := by decide
  have hmB := neg_asr63_andB cp 64#64 hcp63 h3263
  have hmB' := neg_asr63_andB' cp 64#64 hcp63 h3263
  have hoff : (if 64 < cp.toNat then 64 else 0) ≤ 64 := by split <;> omega
  have hl32 : (len - 64#64).toNat = len.toNat - 64 := by rw [BitVec.toNat_sub]; simp; omega
  have hmvok : R.ok (cA "runtime.memmove") [(s.regs 4).toNat - 360, p.toNat + (if 64 < cp.toNat then 64 else 0),
      len.toNat - 64] :=
    hokm (by omega) _ _ _ (by omega)
  have hacc0 : s.mem.accessible (p.toNat + (if 64 < cp.toNat then 64 else 0)) (len.toNat - 64) false = true := by
    split <;> exact Janus.Arm64.Memory.accessible_mono _ hpacc (by omega) (by omega)
  clear hokm
  set_option janus.callRegions true in
  janus64_run [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, htS, hx15, hdf, hmin, hc, hc96, hmB, hmB', hl32,
    toInt_ite, toNat_ite, toInt_small, BitVec.msb_eq_decide] until [segAddr Extracted.program fn + 0x2e5] calls [hmv']
  rename_i _ _ _ _ m _ _ hMFv hLFv hinvv hcp
  have hMFm : MemFrame S.mem m (R.rt ++ win s stk 40) := by
    simp only [win, stk]; janus_frame
  have hd1 := dataLoaded_frame64 hdS (by simp [hrg1]) hro hMFm (fun r hr _ => by
    simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact Janus.Arm64.Memory.accessible_mono _ hwS (Nat.le_refl _) (by omega))
  clear hdS
  have htm : m.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hMFm.readLE _ _ (by simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]; exact ⟨hfsrt, by omega⟩), htS]
    simpa [regG] using hfsg
  have hgm : m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hMFm.readLE _ _ (by simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]; exact ⟨hgr, by omega⟩), hgS]
  have hRA := raSBS impl hap 0x65467a (by decide)
  janus64_run [natLive_zero, hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, htS, htm, hgm, hfs, hx15, hdf, hmin, hc, hc96, hl32,
    toInt_ite, toNat_ite, toInt_small, BitVec.msb_eq_decide] until [pcB3] calls [hP := hS]
  obtain ⟨⟨-, hfs1, hdf1, p1, n1, c1, hp1, hn1, hc1, hv1, hnorm1, hnc1, hnw1, L2, b2, hext2, hb2, hinv2, hlive2, hor2,
    hMF2, hLF2⟩, hd2⟩ := hP
  have bxq := Box.mk (And.intro hga (And.intro hfsw (And.intro hpw (And.intro hcw (And.intro hBuf hor2)))))
  clear hga hfsw hpw hcw hBuf hor2
  simp only [win, setRegF, hspn', ↓reduceIte, Nat.reduceEqDiff] at hMF2 hLF2 hfs1 hdf1
  have hdst : LiveSep L1 [((s.regs 4).toNat - 360, (s.regs 4).toNat - 360 + (len.toNat - 64))] := by
    intro r hr; have := hLsS r hr
    simp only [Outside, and_true] at this ⊢; omega
  have hLFS : LiveFrame S.mem s'.mem L1 [] :=
    (((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.drop hLFv hdst)
      (fun _ _ h => h)).trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => h)).trans
      (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
  refine hk _ L2 b2 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hext.trans hext2) ?_ ?_ ?_ ?_ ?_ ?_)
    (by janus64_simp) (by janus64_simp) (by janus64_simp)
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs1]; exact hfs; done) | (dsimp only; rw [hdf1]; exact hdf.trans hdf0.symm; done) | (simp only [hfs1, hfs]; done) | (simp only [hdf1, hdf, hdf0]; done))
  case h.refine_14 => janus64_callpre
  case h.refine_15 => simp [SetBytesStd.nW] at hb2; exact bud_step hbud hb2
  case h.refine_16 =>
    dsimp only
    rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
      view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
    first | exact hinv2 | exact RtInv.inv_congr hinv2 rfl (by janus64_simp) rfl
  case h.refine_17 => exact hext2.liveSep hLsL1 hwrt
  case h.refine_18 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case h.refine_19 =>
    dsimp only
    exact (hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)).trans
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
      (fun _ _ h => (hext.trans hext2).inRanges_old h)
  case h.refine_20 =>
    intro i hi
    dsimp only
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · refine HdrDone.transport (hhd 0 (by omega)) ?_ ?_ ?_
        (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
          (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
      all_goals (simp only [hdrAt]; janus64_simp)
    · refine HdrDone.transport (hhd 1 (by omega)) ?_ ?_ ?_
        (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
          (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
      all_goals (simp only [hdrAt]; janus64_simp)
    · refine hdrDone_of (m := s'.mem) ?rd
        (hacc := fun a n w => by simp only [Janus.Arm64.Memory.accessible_writeLE, hMF2.accessible, hMFv.accessible, hMF.accessible])
        (by janus64_simp [hp1, hdrAt]) (by janus64_simp [hn1, hdrAt]) (by janus64_simp [hc1, hdrAt]) ?v hnorm1
        (by simpa [SetBytesStd.nW] using hnw1) hnc1 ?fr hlive2 (by rw [hstk]; exact hout)
      case rd =>
        intro a n h
        simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      case fr =>
        intro hc
        rcases bxq.h.2.2.2.2.2 with ⟨-, h⟩ | ⟨h, -⟩
        · simp at h; omega
        · exact h
      case v =>
        have hpw := bxq.h.2.2.1
        rw [hv1, hdrV, show 32 * 2 = 64 from rfl]
        apply beVal_padded
        intro j hj
        simp only [BitVec.toNat_ofNat] at hj
        rw [← Janus.Arm64.Memory.readLE_one]
        unfold padByte
        by_cases hjl : 64 + j < len.toNat
        · rw [if_pos hjl]
          have hcj := hcp j (by omega)
          rw [if_pos (show 64 < cp.toNat by omega)] at hcj
          janus64_simp
          rw [Janus.Arm64.Memory.readLE_one, hcj, ← Janus.Arm64.Memory.readLE_one, ← Janus.Arm64.Memory.readLE_one]
          janus64_simp
          first | done | (rw [Nat.add_assoc]; exact hinS _ _ (by omega) (by omega)) | rw [Nat.add_assoc]
        · rw [if_neg hjl]
          janus64_simp
          rcases (by omega : j < 16 ∨ 16 ≤ j) with h | h <;>
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
            Nat.zero_div, Nat.zero_mod]

end FvModexp.Amd64.Run
