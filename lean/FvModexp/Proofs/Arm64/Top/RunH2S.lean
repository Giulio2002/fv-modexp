import FvModexp.Proofs.Arm64.Top.RunRel

/-! # `Run` (arm64): `B1` to `B2`, `len < 64` (header 1 = `expLen`: `getData(input, 32, 32)`, std `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem h2s (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hokr : HdrOkR R b len)
    (Q : Outcome → Prop)
    (hk : ∀ S L2 b2, RelH R b L c p len cp s ret 2 L2 b2 S → S.pc = BitVec.ofNat 64 pcB2 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 1 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcB1) (h64 : len.toNat < 64) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
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
  janus_data hdS
  have hS := RunCallees.sbStdD impl hap R hmk b1 L1
  have hwT : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwT hok
  have hLS1 : ∀ r ∈ L1, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hBuf : InRanges (BitVec.toNat s.sp - 328) 32 L1 ∨ Outside (BitVec.toNat s.sp - 328) 32 R.rt :=
    Or.inr (hout.of_sub (by omega) (by omega))
  have hspn' : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
  have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by omega)
  have hstk : stk = 4800 := rfl
  by_cases h32 : len.toNat < 32
  · have hmin : min len.toNat 32 = len.toNat := by omega
    have hc : (len.toNat < len.toNat + 32) = True := by simp
    have hmle : (len &&& (len - cp).sshiftRight 63).toNat ≤ len.toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_left
    have hpm : (p + (len &&& (len - cp).sshiftRight 63)).toNat = p.toNat + (len &&& (len - cp).sshiftRight 63).toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hne : ((s.sp - 328#64).toNat = (p + (len &&& (len - cp).sshiftRight 63)).toNat) = False := by
      have hsp328 : (s.sp - 328#64).toNat = s.sp.toNat - 328 := by rw [BitVec.toNat_sub]; simp; omega
      rw [hpm, hsp328]; simp only [eq_iff_iff, iff_false]; omega
    have hne' : (BitVec.toNat s.sp - 328 = (p.toNat + (len.toNat &&& ((len - cp).sshiftRight 63).toNat)) % 18446744073709551616)
        = False := by
      have : (len.toNat &&& ((len - cp).sshiftRight 63).toNat) ≤ len.toNat := Nat.and_le_left
      rw [Nat.mod_eq_of_lt (by omega)]; simp only [eq_iff_iff, iff_false]; omega
    have hoff : (len.toNat &&& ((len - cp).sshiftRight 63).toNat) ≤ len.toNat := Nat.and_le_left
    have hsrc : (p.toNat + (len.toNat &&& ((len - cp).sshiftRight 63).toNat)) % 18446744073709551616 =
        p.toNat + (len.toNat &&& ((len - cp).sshiftRight 63).toNat) := Nat.mod_eq_of_lt (by omega)
    have hacc0 : s.mem.accessible (p.toNat + (len.toNat &&& ((len - cp).sshiftRight 63).toNat)) 0 false = true :=
      Memory.accessible_mono _ hpacc (by omega) (by omega)
    have hmvok : R.ok (cA "runtime.memmove") [s.sp.toNat - 328, p.toNat + (len.toNat &&& ((len - cp).sshiftRight 63).toNat), 0] :=
      hokm (by omega) _ _ _ (by omega)
    clear hokm
    set_option janus.callRegions true in
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, hmin, hc, BitVec.sub_self, natLive_zero, toInt_ite, toNat_ite,
      hne, hne', hsrc, hacc0, toInt_small] until [segAddr Extracted.program fn + 0x150] calls [hmv']
    rename_i m _ _ hMFm hLFm hinvm hcp
    rw [List.append_assoc] at hMFm
    have hd1 := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMFm ?wacc ?ws
    case d0 => janus_callpre
    case wacc => simpa only [Memory.accessible_writeLE] using hwS
    case ws =>
      intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    clear hdS
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, hmin, hc, BitVec.sub_self, natLive_zero, toInt_ite, toNat_ite,
      toInt_small] until [pcB2] calls [hP := hS]
    obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩, hd2⟩ := hP
    simp only [winA, hspn', hspn] at hMF2
    have hdst : LiveSep L1 [(BitVec.toNat s.sp - 328, BitVec.toNat s.sp - 328)] := by
      intro r hr; have := hLsS r hr
      simp only [Outside, and_true] at this ⊢; omega
    have hLFS : LiveFrame S.mem s'.mem L1 [] :=
      ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.drop hLFm hdst)
        (fun _ _ h => h)).trans (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
    refine hk _ L2 b2 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hext.trans hext2) ?_ ?_ ?_ ?_ ?_ ?_) (by janus_simp)
    all_goals try (janus_simp [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2]; done)
    case h.refine_12 => janus_callpre
    case h.refine_13 => simp [SetBytesStd.nW] at hb2; omega
    case h.refine_14 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact RtInv.inv_congr hinv2 rfl (by janus_simp) rfl
    case h.refine_15 => exact hext2.liveSep hLsL1 hwrt
    case h.refine_16 =>
      have hMFm' := hMFm; simp only [← List.append_assoc, List.cons_append, List.nil_append] at hMFm'
      dsimp only; simp only [winA, stk] at hMF ⊢; janus_frame
    case h.refine_17 =>
      dsimp only
      refine ((hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)).trans
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
        (fun _ _ h => (hext.trans hext2).inRanges_old h))
    case h.refine_18 =>
      intro i hi
      dsimp only
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · refine HdrDone.transport (hhd 0 (by omega)) ?_ ?_ ?_
          (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
            (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
        all_goals (simp only [hdrAt]; janus_simp)
      · refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Memory.accessible_writeLE, hMF2.accessible, hMFm.accessible, hMF.accessible])
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
          rw [hv2, hdrV, Nat.mul_one]
          apply beVal_padded
          intro j hj
          simp only [BitVec.toNat_ofNat] at hj
          rw [← Memory.readLE_one]
          unfold padByte
          rw [if_neg (by omega)]
          janus_simp
          rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j) with h | h | h | h <;>
          simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
            Nat.zero_mod]
  · have hmin : min len.toNat 32 = 32 := by omega
    have hc : (len.toNat < 64) = True := by simp; omega
    have hoff : (32 &&& ((32#64 - cp).sshiftRight 63).toNat) ≤ 32 := Nat.and_le_left
    have hne' : (BitVec.toNat s.sp - 328 = (p.toNat + (32 &&& ((32#64 - cp).sshiftRight 63).toNat)) % 18446744073709551616)
        = False := by
      rw [Nat.mod_eq_of_lt (by omega)]; simp only [eq_iff_iff, iff_false]; omega
    have hsrc : (p.toNat + (32 &&& ((32#64 - cp).sshiftRight 63).toNat)) % 18446744073709551616 =
        p.toNat + (32 &&& ((32#64 - cp).sshiftRight 63).toNat) := Nat.mod_eq_of_lt (by omega)
    have hl32 : (len - 32#64).toNat = len.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
    have hacc0 : s.mem.accessible (p.toNat + (32 &&& ((32#64 - cp).sshiftRight 63).toNat)) (len.toNat - 32) false = true :=
      Memory.accessible_mono _ hpacc (by omega) (by omega)
    have hmvok : R.ok (cA "runtime.memmove")
        [s.sp.toNat - 328, p.toNat + (32 &&& ((32#64 - cp).sshiftRight 63).toNat), len.toNat - 32] :=
      hokm (by omega) _ _ _ (by omega)
    clear hokm
    set_option janus.callRegions true in
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, hmin, hc, natLive_zero, toInt_ite, toNat_ite,
      hne', hsrc, hl32, hacc0, toInt_small] until [segAddr Extracted.program fn + 0x150] calls [hmv']
    rename_i m _ _ hMFm hLFm hinvm hcp
    rw [List.append_assoc] at hMFm
    have hd1 := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMFm ?wacc ?ws
    case d0 => janus_callpre
    case wacc => simpa only [Memory.accessible_writeLE] using hwS
    case ws =>
      intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    clear hdS
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2, hgS, hmin, hc, natLive_zero, toInt_ite, toNat_ite,
      hl32, toInt_small] until [pcB2] calls [hP := hS]
    obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩, hd2⟩ := hP
    simp only [winA, hspn', hspn] at hMF2
    have hdst : LiveSep L1 [(BitVec.toNat s.sp - 328, BitVec.toNat s.sp - 328 + (len.toNat - 32))] := by
      intro r hr; have := hLsS r hr
      simp only [Outside, and_true] at this ⊢; omega
    have hLFS : LiveFrame S.mem s'.mem L1 [] :=
      ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.drop hLFm hdst)
        (fun _ _ h => h)).trans (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
    refine hk _ L2 b2 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hext.trans hext2) ?_ ?_ ?_ ?_ ?_ ?_) (by janus_simp)
    all_goals try (janus_simp [hm1, hm2, hm3, hm4, hm5, hm6, hsl1, hsl2]; done)
    case h.refine_12 => janus_callpre
    case h.refine_13 => simp [SetBytesStd.nW] at hb2; omega
    case h.refine_14 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact RtInv.inv_congr hinv2 rfl (by janus_simp) rfl
    case h.refine_15 => exact hext2.liveSep hLsL1 hwrt
    case h.refine_16 =>
      have hMFm' := hMFm; simp only [← List.append_assoc, List.cons_append, List.nil_append] at hMFm'
      dsimp only; simp only [winA, stk] at hMF ⊢; janus_frame
    case h.refine_17 =>
      dsimp only
      refine ((hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)).trans
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
        (fun _ _ h => (hext.trans hext2).inRanges_old h))
    case h.refine_18 =>
      intro i hi
      dsimp only
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · refine HdrDone.transport (hhd 0 (by omega)) ?_ ?_ ?_
          (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
            (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
        all_goals (simp only [hdrAt]; janus_simp)
      · refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Memory.accessible_writeLE, hMF2.accessible, hMFm.accessible, hMF.accessible])
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
          rw [hv2, hdrV, Nat.mul_one]
          apply beVal_padded
          intro j hj
          simp only [BitVec.toNat_ofNat] at hj
          rw [← Memory.readLE_one]
          unfold padByte
          split
          · rename_i hjl
            have hM : (32 &&& ((32#64 - cp).sshiftRight 63).toNat) = 32 :=
              sliceMask_lt 32 32#64 cp (by simp; omega) (by omega) (by omega)
            have hcj := hcp j (by omega)
            rw [hM] at hcj
            janus_simp
            rw [Memory.readLE_one, hcj, ← Memory.readLE_one, ← Memory.readLE_one]
            rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
              Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
              Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
              Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
            rw [Nat.add_assoc]; exact hinS _ _ (by omega) (by omega)
          · rename_i hjl
            janus_simp
            rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j) with h | h | h | h <;>
            simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
              Nat.zero_mod]

end FvModexp.Arm64.Run
