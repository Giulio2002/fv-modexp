import FvModexp.Proofs.Arm64.Top.RunDRel
import FvModexp.Proofs.Arm64.Top.RunL
import FvModexp.Proofs.Arm64.Top.RunD1

/-! # `Run` (arm64): `C0` to `D1`, base operand shorter than the input rest: padded buffer (stack or `makeslice`), `memmove` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem d1p (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.pc = BitVec.ofNat 64 pcC0) (hTm : T.mem = S.mem) (hTsp : T.sp = S.sp)
    (hT28 : T.regs 28 = S.regs 28) (hT29 : T.regs 29 = S.regs 29) (hT18 : T.regs 18 = S.regs 18)
    (hl0 : hdrV s p len 0 ≤ 1024) (hl1 : hdrV s p len 1 ≤ 1024) (hl2 : hdrV s p len 2 ≤ 1024)
    (hnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (hr8 : (T.regs 8).toNat = hdrV s p len 0) (hr11 : (T.regs 11).toNat = hdrV s p len 1)
    (hr12 : (T.regs 12).toNat = hdrV s p len 2)
    (hr1 : (T.regs 1).toNat = p.toNat + (if 96 < len.toNat then 96 else 0))
    (hr3 : (T.regs 3).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0)) (hr7 : (T.regs 7).toNat = len.toNat - 96)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b) (hndir : len.toNat - 96 < hdrV s p len 0) (hsm0 : hdrV s p len 0 ≤ 32)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 1 L2 b2 S2 → S2.pc = BitVec.ofNat 64 pcD1 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, -, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF,
    -⟩ := hrel
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
  have hI7 := toInt_small (T.regs 7) (by omega)
  have hI8 := toInt_small (T.regs 8) (by omega)
  have hI11 := toInt_small (T.regs 11) (by omega)
  have hI12 := toInt_small (T.regs 12) (by omega)
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      unfold Apart at hga; exact ⟨hgr, by omega, by omega⟩)
  have hwS : S.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : S.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hga
  have hwT : Outside SetBytes.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytes.wordT
  rw [h_t] at hwT hokS
  have hLS1 : ∀ r ∈ L1, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hS := RunCallees.sbFixD impl hap R hmk b1 L1
  have hr8' : T.regs 8 = BitVec.ofNat 64 (hdrV s p len 0) := by
    apply BitVec.eq_of_toNat_eq; rw [hr8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hc : (len.toNat - 96 < hdrV s p len 0) = True := by simp; omega
  by_cases hsm : hdrV s p len 0 ≤ 32
  · have hc32 : (32 < hdrV s p len 0) = False := by simp; omega
    have hmvok : R.ok (cA "runtime.memmove") [s.sp.toNat - 392, (T.regs 1).toNat, len.toNat - 96] :=
      hokM _ _ _ (by omega)
    have hne : (BitVec.toNat s.sp - 392 = (T.regs 1).toNat) = False := by
      simp only [eq_iff_iff, iff_false]; rw [hr1]; split <;> omega
    have hne' : ((T.regs 1).toNat = BitVec.toNat s.sp - 392) = False := by
      simp only [eq_iff_iff, iff_false]; rw [hr1]; split <;> omega
    have hs1 : (T.regs 1).toNat + (len.toNat - 96) ≤ 2 ^ 48 := by rw [hr1]; split <;> omega
    have hs2 : s.mem.accessible (T.regs 1).toNat (len.toNat - 96) false = true := by
      rw [hr1]; exact Memory.accessible_mono _ hpacc (by split <;> omega) (by split <;> omega)
    have hs3 : (T.regs 1).toNat + (len.toNat - 96) ≤ BitVec.toNat s.sp - 624 - 4096 ∨
        BitVec.toNat s.sp - 624 - 8 ≤ (T.regs 1).toNat := by rw [hr1]; split <;> omega
    have hs4 : (T.regs 1).toNat + (len.toNat - 96) ≤ BitVec.toNat s.sp - 624 + 8 ∨
        BitVec.toNat s.sp - 624 + 8 + 24 ≤ (T.regs 1).toNat := by rw [hr1]; split <;> omega
    set_option janus.callRegions true in
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, hr7, hr8', hr11, hr12, hI7, hI8, hI11, hI12, hc, hc32, hne, hne',
      natLive_zero, toInt_ite, toNat_ite] until [segAddr Extracted.program fn + 0x4dc] calls [hmv']
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
    have hH : InRanges (BitVec.toNat s.sp - 392) (hdrV s p len 0) L1 ∨ Outside (BitVec.toNat s.sp - 392) (hdrV s p len 0) R.rt :=
      Or.inr (hout.of_sub (by omega) (by omega))
    have hW : BitVec.toNat s.sp - 392 + hdrV s p len 0 ≤ BitVec.toNat s.sp - 624 - 4160 ∨
        BitVec.toNat s.sp - 624 + 48 ≤ BitVec.toNat s.sp - 392 := by omega
    have hokm : R.ok (cA "runtime.makeslice") [2641088, SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0)),
        makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0)))] := hokS _ (by simp [SetBytes.nW]; omega)
    have hMC0 : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0))) ≤ allocCost (8 * 132) := by
      have h1 : SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0)) ≤ 128 := by simp [SetBytes.nW]; omega
      have h3 : makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0))) ≤ 132 := by unfold makeCap; split <;> omega
      simp only [makeCost, allocCost]; omega
    have hMC : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0))) ≤ b1 := by
      simp only [dCost] at hbudD; omega
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, hr7, hr8', hr11, hr12, hI7, hI8, hI11, hI12, hc, hc32, natLive_zero,
      toInt_ite, toNat_ite] until [pcD1] calls [hP := hS]
    obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩,
      hd2⟩ := hP
    have hspn' : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [winA, hspn', hspn] at hMF2
    have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
    have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    have hstk : stk = 4800 := rfl
    have hdst : LiveSep L1 [(BitVec.toNat s.sp - 392, BitVec.toNat s.sp - 392 + (len.toNat - 96))] := by
      intro r hr; have := hLsS r hr
      simp only [Outside, and_true] at this ⊢; omega
    have hLFS : LiveFrame S.mem s'.mem L1 [] :=
      (((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.drop hLFm hdst)
        (fun _ _ h => h)).trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => h)).trans
        (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
    refine hk _ L2 b2 (RelD.mk' hin0 (by janus_simp [hsp]) (by janus_simp [h28, hT28]) (by janus_simp [h29, hT29])
      (by janus_simp [h18, hT18]) (by janus_simp [hm1]) (by janus_simp [hm2]) (by janus_simp [hm3]) (by janus_simp [hm4])
      (by janus_simp [hm5]) (by janus_simp [hm6]) (by janus_simp [hr8]) (by janus_simp [hr11]) (by janus_simp [hr12])
      (by janus_simp [hr7]) (by janus_simp [hr3]) (by janus_simp [hr1]) hl0 hl1 hl2 hnz ?_ (fun h => absurd h (by decide)) ?_ (hext.trans hext2) ?_ ?_
      (hext2.liveSep hLsL1 hwrt) ?_ ?_ ?_) (by janus_simp)
    · intro _
      have hmin : min (hdrV s p len 0) (len.toNat - 96) = len.toNat - 96 := by omega
      rw [hmin]; constructor <;> (janus_simp; try omega)
    · janus_callpre
    · simp only [dCost] at hbudD ⊢; omega
    · dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact RtInv.inv_congr hinv2 rfl (by janus_simp) rfl
    · have hMFm' := hMFm; simp only [← List.append_assoc, List.cons_append, List.nil_append] at hMFm'
      dsimp only; simp only [winA, stk] at hMF ⊢; janus_frame
    · dsimp only
      exact (hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)).trans
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
        (fun _ _ h => (hext.trans hext2).inRanges_old h)
    · intro j hj
      obtain rfl : j = 0 := by omega
      dsimp only
      refine opDone_of (m := s'.mem) ?rd (hacc := fun a n w => by
          simp only [Memory.accessible_writeLE, hMF2.accessible, hMFm.accessible, hMF.accessible])
        (by janus_simp [opAt]) (by janus_simp [hp2, opAt]) (by janus_simp [hn2, opAt]) (by janus_simp [hc2, opAt]) ?v hnorm2
        (by simp only [SetBytes.nW, BitVec.toNat_ofNat] at hnw2; omega) hnc2 ?fr hlive2 (by rw [hstk]; exact hout)
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
        rw [hv2]
        simp only [opV, opStart, opLen, if_pos, Nat.add_zero]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        apply beVal_padded
        intro j hj
        rw [← Memory.readLE_one, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        unfold padByte
        split
        · rename_i hjl
          have hcj := hcp j (by omega)
          rw [Memory.readLE_one, hcj, ← Memory.readLE_one, hr1, if_pos (by omega)]
          repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
          rw [hinS _ _ (by omega) (by omega), Memory.readLE_one, Nat.add_assoc]
        · rename_i hjl
          rw [hMFm.readLE _ _ (by
            simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
            exact ⟨hout.of_sub (by omega) (by omega), by omega⟩)]
          rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j) with h | h | h | h <;>
          simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
            Nat.zero_mod]
  · exact absurd hsm0 hsm

end FvModexp.Arm64.Run
