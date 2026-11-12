import FvModexp.Proofs.Amd64.Top.RunRel

/-! # `Run` (amd64): entry to the first boundary `B1` (prologue, header 0 = `baseLen`: `getData`, std `setBytes`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem h1 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (hs : CallSetup ((LibRun.program.link impl).withExit ret) (segAddr Extracted.program fn) [c, p, len, cp] s)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (hokr : HdrOkR R b len)
    (Q : Janus.Amd64.Outcome → Prop)
    (hk : ∀ S L1 b1, RelH R b L c p len cp s ret 1 L1 b1 S → S.rip = BitVec.ofNat 64 pcB1 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q) :
    Reaches ((LibRun.program.link impl).withExit ret) s Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hok, hcost, hokm⟩ := hokr
  have hmv' : MemmoveLive64 (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmv
  have hLs0 := hLs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw
  janus64_intro hs
  simp only [LiveSep, win] at hLs
  simp only [win, Outside, and_true] at hpw hcw
  unfold Apart at hga
  have hS := RunCallees.sbStdD impl hap R hmk b L
  have hwS : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwS hok
  have hLS1 : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ BitVec.toNat (s.regs 4) - 616 - 4160 ∨
      BitVec.toNat (s.regs 4) - 616 + 48 ≤ r.fst := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; omega
  have hBuf : InRanges (BitVec.toNat (s.regs 4) - 296) 32 L ∨ Outside (BitVec.toNat (s.regs 4) - 296) 32 R.rt :=
    Or.inr (hout.of_sub (by omega) (by omega))
  obtain ⟨⟨hfs8, hfsacc, hfsg⟩, hfsrt, hfsw⟩ := htls
  unfold Apart at hfsw
  by_cases h32 : len.toNat < 32
  · have hmvok : R.ok (cA "runtime.memmove") [(s.regs 4).toNat - 296, p.toNat, len.toNat] :=
      hokm (by omega) _ _ _ (by omega)
    have hc : (len.toNat < 32) = True := by simp; omega
    clear hokm
    set_option janus.callRegions true in
    janus64_run [toInt_ite, toNat_ite, toInt_small, hc, BitVec.msb_eq_decide] until [segAddr Extracted.program fn + 0xde] calls [hmv']
    rename_i _ _ _ _ m _ _ hMF hLF hinv1 hcp
    have hMFm : MemFrame s.mem m (R.rt ++ win s stk 40) := by
      simp only [win, stk]; janus_frame
    have hd1 := dataLoaded_frame64 hd (by simp [hrg1]) hro hMFm (fun r hr _ => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega))
    clear hd
    have hRA := raSBS impl hap 0x654450 (by decide)
    janus64_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc, BitVec.msb_eq_decide] until [pcB1] calls [hP := hS]
    obtain ⟨⟨-, hfs1, hdf1, p1, n1, c1, hp1, hn1, hc1, hv1, hnorm1, hnc1, hnw1, L1, b1, hext1, hb1, hinv2, hlive1, hor1, hMF1, hLF1⟩, hd1⟩ := hP
    have hspn : (s.regs 4 - 616#64).toNat = (s.regs 4).toNat - 616 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [win, setRegF, hspn, ↓reduceIte, Nat.reduceEqDiff] at hMF1 hLF1 hfs1 hdf1
    refine hk _ L1 b1 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hext1 ?_ ?_ ?_ ?_ ?_ ?_) (by janus64_simp)
    all_goals try (janus64_simp; done)
    all_goals try (first | (dsimp only; rw [hfs1]; done) | (dsimp only; rw [hdf1]; done) | (simp only [hfs1]; done) | (simp only [hdf1]; done))
    case refine_13 => intro _; refine ⟨?_, ?_⟩ <;> (janus64_simp; try omega)
    case refine_14 => janus64_callpre
    case refine_15 => simpa [SetBytesStd.nW] using hb1
    case refine_16 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact hinv2
    case refine_17 => exact hext1.liveSep hLs0 (fun r hr => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega))
    case refine_18 => dsimp only; simp only [win, stk]; janus_frame
    case refine_19 =>
      dsimp only
      have hdst : LiveSep L [((s.regs 4).toNat - 296, (s.regs 4).toNat - 296 + len.toNat)] := by
        intro r hr; have := hLs r hr
        simp only [Outside, and_true] at this ⊢; omega
      refine ((((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLs0).trans (LiveFrame.drop hLF hdst)
        (fun _ _ h => h)).trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLs0) (fun _ _ h => h)).trans
        (LiveFrame.of_empty hLF1 []) (fun _ _ h => h)).trans
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext1.liveSep hLs0 ?_))
        (fun _ _ h => hext1.inRanges_old h)
      intro r hr
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    case refine_20 =>
      intro i hi
      obtain rfl : i = 0 := by omega
      dsimp only
      have hstk : stk = 4800 := rfl
      refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Janus.Arm64.Memory.accessible_writeLE, hMF1.accessible, hMF.accessible])
          (by janus64_simp [hp1, hdrAt]) (by janus64_simp [hn1, hdrAt]) (by janus64_simp [hc1, hdrAt]) ?v hnorm1
        (by simpa [SetBytesStd.nW] using hnw1) hnc1 ?fr hlive1 (by rw [hstk]; exact hout)
      case rd =>
        intro a n h
        simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      case fr =>
        intro hc
        rcases hor1 with ⟨-, h⟩ | ⟨h, -⟩
        · simp at h; omega
        · exact h
      case v =>
        rw [hv1, hdrV, Nat.mul_zero]
        apply beVal_padded
        intro j hj
        simp only [BitVec.toNat_ofNat] at hj
        rw [← Janus.Arm64.Memory.readLE_one]
        unfold padByte
        split
        · rename_i hjl
          have hcj := hcp j (by omega)
          janus64_simp
          rw [Janus.Arm64.Memory.readLE_one, hcj, ← Janus.Arm64.Memory.readLE_one, ← Janus.Arm64.Memory.readLE_one]
          janus64_simp
        · rename_i hjl
          janus64_simp
          simp only [Nat.zero_add] at hjl
          have hj32 : j < 32 := by omega
          rcases (by omega : j < 16 ∨ 16 ≤ j) with h | h <;>
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside, Nat.zero_div,
            Nat.zero_mod]
  · have hH0 : InRanges p.toNat 32 L ∨ Outside p.toNat 32 R.rt := hheld.sub (Nat.le_refl _) (by omega)
    have hc : (len.toNat < 32) = False := by simp; omega
    clear hokm
    have hRA := raSBS impl hap 0x654450 (by decide)
    janus64_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc, BitVec.msb_eq_decide] until [pcB1] calls [hP := hS]
    obtain ⟨⟨-, hfs1, hdf1, p1, n1, c1, hp1, hn1, hc1, hv1, hnorm1, hnc1, hnw1, L1, b1, hext1, hb1, hinv1, hlive1, hor1, hMF1, hLF1⟩, hd1⟩ := hP
    have hspn : (s.regs 4 - 616#64).toNat = (s.regs 4).toNat - 616 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [win, setRegF, hspn, ↓reduceIte, Nat.reduceEqDiff] at hMF1 hLF1 hfs1 hdf1
    refine hk _ L1 b1 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hext1 ?_ ?_ ?_ ?_ ?_ ?_) (by janus64_simp)
    all_goals try (janus64_simp; done)
    all_goals try (first | (dsimp only; rw [hfs1]; done) | (dsimp only; rw [hdf1]; done) | (simp only [hfs1]; done) | (simp only [hdf1]; done))
    case refine_13 => intro _; refine ⟨?_, ?_⟩ <;> (janus64_simp; try omega)
    case refine_14 => janus64_callpre
    case refine_15 => simpa [SetBytesStd.nW] using hb1
    case refine_16 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact hinv1
    case refine_17 => exact hext1.liveSep hLs0 (fun r hr => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega))
    case refine_18 => dsimp only; simp only [win, stk]; janus_frame
    case refine_19 =>
      dsimp only
      refine ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLs0).trans (LiveFrame.of_empty hLF1 [])
        (fun _ _ h => h)).trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext1.liveSep hLs0 ?_))
        (fun _ _ h => hext1.inRanges_old h)
      intro r hr
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    case refine_20 =>
      intro i hi
      obtain rfl : i = 0 := by omega
      dsimp only
      have hstk : stk = 4800 := rfl
      refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Janus.Arm64.Memory.accessible_writeLE, hMF1.accessible])
          (by janus64_simp [hp1, hdrAt]) (by janus64_simp [hn1, hdrAt]) (by janus64_simp [hc1, hdrAt]) ?v hnorm1
        (by simpa [SetBytesStd.nW] using hnw1) hnc1 ?fr hlive1 (by rw [hstk]; exact hout)
      case rd =>
        intro a n h
        simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      case fr =>
        intro hc
        rcases hor1 with ⟨-, h⟩ | ⟨h, -⟩
        · simp at h; omega
        · exact h
      case v =>
        rw [hv1, hdrV, Nat.mul_zero, padBE_inside _ _ _ _ _ (by omega), Nat.add_zero]
        apply beVal_of_reads
        intro i hi
        simp only [BitVec.toNat_ofNat] at hi
        janus64_simp

end FvModexp.Amd64.Run
