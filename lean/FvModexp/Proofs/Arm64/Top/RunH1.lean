import FvModexp.Proofs.Arm64.Top.RunRel
import FvModexp.Proofs.Arm64.Top.RunSmall

/-! # `Run` (arm64): entry to the first boundary `B1` (prologue, header 0 = `baseLen`: `getData`, std `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem h1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (hs : CallSetup ((LibRun.program.link impl).withExit ret) (segAddr Extracted.program fn) [c, p, len, cp] s)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) (hokr : HdrOkR R b len)
    (Q : Outcome → Prop)
    (hk : ∀ S L1 b1, RelH R b L c p len cp s ret 1 L1 b1 S → S.pc = BitVec.ofNat 64 pcB1 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q) :
    Reaches ((LibRun.program.link impl).withExit ret) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hok, hcost, hokm⟩ := hokr
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hmvD := MemmoveLive.withData hmv' hro
  have hap1 := hap.1
  have hLs0 := hLs
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw
  janus_intro hs
  simp only [LiveSep, win] at hLs
  simp only [win, Outside, and_true] at hpw hcw
  unfold Apart at hga
  have hS := RunCallees.sbStdD impl hap R hmk b L
  have hwS : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwS hok
  have hLS1 : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; omega
  have hBuf : InRanges (BitVec.toNat s.sp - 296) 32 L ∨ Outside (BitVec.toNat s.sp - 296) 32 R.rt :=
    Or.inr (hout.of_sub (by omega) (by omega))
  by_cases h32 : len.toNat < 32
  · have hmvok : R.ok (cA "runtime.memmove") [s.sp.toNat - 296, p.toNat, len.toNat] := hokm (by omega) _ _ _ (by omega)
    have hc : (len.toNat < 32) = True := by simp; omega
    clear hokm
    set_option janus.callRegions true in
    janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc] until [segAddr Extracted.program fn + 0x8c] calls [hmv']
    rename_i _ _ _ m _ _ hMF hLF hinv1 hcp
    rw [List.append_assoc] at hMF
    have hd1 := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMF ?w ?ws
    case d0 => janus_callpre
    case w => simpa only [Memory.accessible_writeLE] using hw
    case ws =>
      intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    clear hd
    have hRA := raSBS impl hap 0x203194 (by decide)
    janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc] until [pcB1] calls [hP := hS]
    obtain ⟨⟨-, p1, n1, c1, hp1, hn1, hc1, hv1, hnorm1, hnc1, hnw1, L1, b1, hext1, hb1, hinv1, hlive1, hor1, hMF1, hLF1⟩, hd1⟩ := hP
    have hspn : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [winA, hspn] at hMF1
    refine hk _ L1 b1 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hext1 ?_ ?_ ?_ ?_ ?_ ?_) (by janus_simp)
    all_goals try (janus_simp; done)
    case refine_11 => intro _; refine ⟨?_, ?_⟩ <;> (janus_simp; try omega)
    case refine_12 => janus_callpre
    case refine_13 => simpa [SetBytesStd.nW] using hb1
    case refine_14 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact hinv1
    case refine_15 => exact hext1.liveSep hLs0 (fun r hr => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega))
    case refine_16 =>
      have hMF' := hMF; simp only [← List.append_assoc, List.cons_append, List.nil_append] at hMF'
      dsimp only; simp only [winA, stk]
      janus_frame
    case refine_17 =>
      dsimp only
      have hdst : LiveSep L [(BitVec.toNat s.sp - 296, BitVec.toNat s.sp - 296 + len.toNat)] := by
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
    case refine_18 =>
      intro i hi
      obtain rfl : i = 0 := by omega
      dsimp only
      have hstk : stk = 4800 := rfl
      refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Memory.accessible_writeLE, hMF1.accessible, hMF.accessible])
          (by janus_simp [hp1, hdrAt]) (by janus_simp [hn1, hdrAt]) (by janus_simp [hc1, hdrAt]) ?v hnorm1
        (by simpa [SetBytesStd.nW] using hnw1) hnc1 ?fr hlive1 (by rw [hstk]; exact hout)
      case rd =>
        intro a n h
        simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
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
        rw [← Memory.readLE_one]
        unfold padByte
        split
        · rename_i hjl
          have hcj := hcp j (by omega)
          janus_simp
          rw [Memory.readLE_one, hcj, ← Memory.readLE_one, ← Memory.readLE_one]
          janus_simp
        · rename_i hjl
          janus_simp
          simp only [Nat.zero_add] at hjl
          have hj32 : j < 32 := by omega
          rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j) with h | h | h | h <;>
          simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
            Nat.zero_mod]
  · have hH0 : InRanges p.toNat 32 L ∨ Outside p.toNat 32 R.rt := hheld.sub (Nat.le_refl _) (by omega)
    have hW0 : p.toNat + 32 ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ p.toNat := by omega
    have hc : (len.toNat < 32) = False := by simp; omega
    clear hokm
    have hRA := raSBS impl hap 0x203194 (by decide)
    janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc] until [pcB1] calls [hP := hS]
    obtain ⟨⟨-, p1, n1, c1, hp1, hn1, hc1, hv1, hnorm1, hnc1, hnw1, L1, b1, hext1, hb1, hinv1, hlive1, hor1, hMF1, hLF1⟩, hd1⟩ := hP
    have hspn : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [winA, hspn] at hMF1
    refine hk _ L1 b1 (RelH.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hext1 ?_ ?_ ?_ ?_ ?_ ?_) (by janus_simp)
    all_goals try (janus_simp; done)
    case refine_11 => intro _; refine ⟨?_, ?_⟩ <;> (janus_simp; try omega)
    case refine_12 => janus_callpre
    case refine_13 => simpa [SetBytesStd.nW] using hb1
    case refine_14 =>
      dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact hinv1
    case refine_15 => exact hext1.liveSep hLs0 (fun r hr => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega))
    case refine_16 => dsimp only; simp only [winA, stk]; janus_frame
    case refine_17 =>
      dsimp only
      refine ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLs0).trans (LiveFrame.of_empty hLF1 [])
        (fun _ _ h => h)).trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext1.liveSep hLs0 ?_))
        (fun _ _ h => hext1.inRanges_old h)
      intro r hr
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    case refine_18 =>
      intro i hi
      obtain rfl : i = 0 := by omega
      dsimp only
      have hstk : stk = 4800 := rfl
      refine hdrDone_of (m := s'.mem) ?rd (hacc := fun a n w => by simp only [Memory.accessible_writeLE, hMF1.accessible])
          (by janus_simp [hp1, hdrAt]) (by janus_simp [hn1, hdrAt]) (by janus_simp [hc1, hdrAt]) ?v hnorm1
        (by simpa [SetBytesStd.nW] using hnw1) hnc1 ?fr hlive1 (by rw [hstk]; exact hout)
      case rd =>
        intro a n h
        simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
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
        janus_simp

end FvModexp.Arm64.Run
