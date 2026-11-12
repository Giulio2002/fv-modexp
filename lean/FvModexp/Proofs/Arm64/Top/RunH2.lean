import FvModexp.Proofs.Arm64.Top.RunH2S
import FvModexp.Proofs.Arm64.Top.RunSmall

/-! # `Run` (arm64): `B1` to `B2` (header 1 = `expLen`: `getData(input, 32, 32)`, std `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem h2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hokr : HdrOkR R b len)
    (Q : Outcome → Prop)
    (hk : ∀ S L2 b2, RelH R b L c p len cp s ret 2 L2 b2 S → S.pc = BitVec.ofNat 64 pcB2 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 1 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcB1) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  by_cases h64' : len.toNat < 64
  · exact h2s impl hap R hmk hmv b L c p len cp ret hret s henv hin hokr Q hk S L1 b1 hrel hpc h64'
  have h64 : 64 ≤ len.toNat := by omega
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hok, hcost, hokm⟩ := hokr
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hsl, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF,
    hhd⟩ := hrel
  obtain ⟨hsl1, hsl2⟩ := hsl (Nat.le_refl _)
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [LiveSep, win] at hLsS
  simp only [win, Outside, and_true] at hpw hcw
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      unfold Apart at hga; exact ⟨hgr, by omega, by omega⟩)
  have hwS : S.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : S.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hga
  have hS := RunCallees.sbStdD impl hap R hmk b1 L1
  have hwT : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwT hok
  have hLS1 : ∀ r ∈ L1, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  · have hH1 : InRanges (p.toNat + 32) 32 L ∨ Outside (p.toNat + 32) 32 R.rt := hheld.sub (by omega) (by omega)
    have hH1' : InRanges (p.toNat + 32) 32 L1 ∨ Outside (p.toNat + 32) 32 R.rt := hext.held hH1
    have hW1 : p.toNat + 32 + 32 ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ p.toNat + 32 := by omega
    have hc32 : (len.toNat < 32) = False := by simp; omega
    have hc64 : (len.toNat < 64) = False := by simp; omega
    have hmin : min len.toNat 32 = 32 := by omega
    have hRA := raSBS impl hap 0x20324c (by decide)
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, hmin, natLive_zero, toInt_ite, toNat_ite, toInt_small, hc32, hc64,
      sliceMask_lt, sliceMask_eq] until [pcB2]
      calls [hP := hS]
    obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩, hd2⟩ := hP
    have hspn' : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [winA, hspn', hspn] at hMF2
    have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
    have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    refine hk _ L2 b2 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hext.trans hext2) ?_ ?_ ?_ ?_ ?_ ?_) (by janus_simp)
    all_goals try (janus_simp [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2]; done)
    case refine_12 => janus_callpre
    case refine_13 => simp [SetBytesStd.nW] at hb2; first | exact bud_step hbud hb2 | omega
    case refine_14 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact RtInv.inv_congr hinv2 rfl (by janus_simp) rfl
    case refine_15 => exact hext2.liveSep hLsL1 hwrt
    case refine_16 => dsimp only; simp only [winA, stk] at hMF ⊢; janus_frame
    case refine_17 =>
      dsimp only
      refine (((hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => hext.inRanges_old h)).trans
        (LiveFrame.of_empty hLF2 []) (fun _ _ h => hext.inRanges_old h)).trans
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
        (fun _ _ h => (hext.trans hext2).inRanges_old h))
    case refine_18 =>
      have hstk : stk = 4800 := rfl
      have hmask : (32#64 &&& (32#64 - cp).sshiftRight 63) = 32#64 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]
        exact sliceMask_lt 32 32#64 cp (by simp; omega) (by omega) (by omega)
      rw [hmask] at hv2
      intro i hi
      dsimp only
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · refine HdrDone.transport (hhd 0 (by omega)) ?_ ?_ ?_
          (((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans
            (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)).trans
            (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
            (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
        all_goals (simp only [hdrAt]; janus_simp)
      · refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Memory.accessible_writeLE, hMF2.accessible, hMF.accessible])
          (by janus_simp [hp2, hdrAt]) (by janus_simp [hn2, hdrAt])
          (by janus_simp [hc2, hdrAt]) ?v hnorm2 (by simpa [SetBytesStd.nW] using hnw2) hnc2 ?fr hlive2
          (by rw [hstk]; exact hout)
        case rd =>
          intro a n h
          simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
          rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        case fr =>
          intro hc
          rcases hor2 with ⟨-, h⟩ | ⟨h, -⟩
          · simp at h; omega
          · exact h
        case v =>
          have hp32 : (p + 32#64).toNat = p.toNat + 32 := by rw [BitVec.toNat_add]; simp; omega
          rw [hv2, hdrV, padBE_inside _ _ _ _ _ (by omega), hp32, Nat.mul_one]
          apply beVal_of_reads
          intro i hi
          simp only [BitVec.toNat_ofNat] at hi
          dsimp only
          rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
          exact hinS _ _ (by omega) (by omega)

end FvModexp.Arm64.Run
