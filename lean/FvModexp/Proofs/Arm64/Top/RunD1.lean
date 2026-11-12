import FvModexp.Proofs.Arm64.Top.RunDPc
import FvModexp.Proofs.Arm64.Top.RunL
import FvModexp.Proofs.Arm64.Top.RunBox

/-! # `Run` (arm64): `C0` to `D1` — the base operand (`getData(input, 0, baseLen)`, patched `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d1x (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b) (hdir0 : hdrV s p len 0 ≤ len.toNat - 96)
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
    gS_read hMF hga hgr
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
  by_cases hdir : hdrV s p len 0 ≤ len.toNat - 96
  · have hc : (len.toNat - 96 < hdrV s p len 0) = False := by simp; omega
    have hH : InRanges (T.regs 1).toNat (hdrV s p len 0) L1 ∨ Outside (T.regs 1).toNat (hdrV s p len 0) R.rt := by
      rw [hr1]; exact hext.held (hheld.sub (by split <;> omega) (by split <;> omega))
    have hW : (T.regs 1).toNat + hdrV s p len 0 ≤ BitVec.toNat s.sp - 624 - 4160 ∨
        BitVec.toNat s.sp - 624 + 48 ≤ (T.regs 1).toNat := by
      rw [hr1]; split <;> omega
    have hokm : R.ok (cA "runtime.makeslice") [2641088, SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0)),
        makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0)))] := hokS _ (by simp [SetBytes.nW]; omega)
    have hB48 : (T.regs 1).toNat + hdrV s p len 0 ≤ 2 ^ 48 := by rw [hr1]; split <;> omega
    have hAcc : s.mem.accessible (T.regs 1).toNat (hdrV s p len 0) false = true := by
      rw [hr1]; exact Memory.accessible_mono _ hpacc (by split <;> omega) (by split <;> omega)
    have hMC0 : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0))) ≤ allocCost (8 * 132) := by
      have h1 : SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0)) ≤ 128 := by simp [SetBytes.nW]; omega
      have h3 : makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0))) ≤ 132 := by unfold makeCap; split <;> omega
      simp only [makeCost, allocCost]; omega
    have hMC : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 0))) ≤ b1 := by
      simp only [dCost] at hbudD; omega
    janus_data hdS
    have hRA := raSB impl hap 0x2035e8 (by decide)
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, hr7, hr8', hr11, hr12, hI7, hI8, hI11, hI12, hc, natLive_zero, toInt_ite,
      toNat_ite] until [pcD1] calls [hP := hS]
    obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩,
      hd2⟩ := hP
    have bxpw := Box.mk hpw; have bxcw := Box.mk hcw; have bxga := Box.mk hga; have bxW := Box.mk hW
    have bxH := Box.mk hH; have bxnz := Box.mk hnz; have bxor := Box.mk hor2
    clear hpw hcw hga hW hH hnz hor2
    have hspn' : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [winA, hspn', hspn] at hMF2
    have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
    have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    have hstk : stk = 4800 := rfl
    have hLFS : LiveFrame S.mem s'.mem L1 [] :=
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
    refine hk _ L2 b2 (RelD.mk' hin0 (by janus_simp [hsp]) (by janus_simp [h28, hT28]) (by janus_simp [h29, hT29])
      (by janus_simp [h18, hT18]) (by janus_simp [hm1]) (by janus_simp [hm2]) (by janus_simp [hm3]) (by janus_simp [hm4])
      (by janus_simp [hm5]) (by janus_simp [hm6]) (by janus_simp [hr8]) (by janus_simp [hr11]) (by janus_simp [hr12])
      (by janus_simp [hr7]) (by janus_simp [hr3]) (by janus_simp [hr1]) hl0 hl1 hl2 bxnz.h ?_ (fun h => absurd h (by decide)) ?_ (hext.trans hext2) ?_ ?_
      (hext2.liveSep hLsL1 hwrt) ?_ ?_ ?_ (opsApart_one _ _)) (by janus_simp)
    · intro _
      have hmin : min (hdrV s p len 0) (len.toNat - 96) = hdrV s p len 0 := by omega
      rw [hmin]; constructor <;> (janus_simp; try omega)
    · janus_callpre
    · simp only [dCost] at hbudD ⊢; omega
    · dsimp only
      rw [view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega)),
        view_writeLE_out (hout.of_sub (by omega) (by omega)), view_writeLE_out (hout.of_sub (by omega) (by omega))]
      exact RtInv.inv_congr hinv2 rfl (by janus_simp) rfl
    · dsimp only; simp only [winA, stk] at hMF ⊢; janus_frame
    · dsimp only
      exact (hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)).trans
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
        (fun _ _ h => (hext.trans hext2).inRanges_old h)
    · intro j hj
      obtain rfl : j = 0 := by omega
      dsimp only
      refine opDone_of (m := s'.mem) (hLc := hext) ?rd (hacc := fun a n w => by
          simp only [Memory.accessible_writeLE, hMF2.accessible, hMF.accessible])
        (by janus_simp [opAt]) (by janus_simp [hp2, opAt]) (by janus_simp [hn2, opAt]) (by janus_simp [hc2, opAt]) ?v hnorm2
        (by simp only [SetBytes.nW, BitVec.toNat_ofNat] at hnw2; omega) hnc2 ?fr hlive2 (by rw [hstk]; exact hout)
      case rd =>
        intro a n h
        simp only [win, hstk, Janus.outside_cons, Janus.outside_nil, and_true] at h
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      case fr =>
        intro hc
        rcases bxor.h with ⟨-, h⟩ | ⟨h, h'⟩
        · simp at h; omega
        · exact ⟨h, h'⟩
      case v =>
        rw [hv2]
        simp only [opV, opStart, opLen, if_pos, Nat.add_zero]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hr1]
        by_cases h96 : 96 < len.toNat
        · have hpw := bxpw.h; have hW := bxW.h
          rw [if_pos h96, padBE_inside _ _ _ _ _ (by omega)]
          apply beVal_of_reads
          intro i hi
          repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
          exact hinS _ _ (by omega) (by omega)
        · have h0 : hdrV s p len 0 = 0 := by omega
          rw [h0]; rfl
  · exact absurd hdir0 hdir

end FvModexp.Arm64.Run
