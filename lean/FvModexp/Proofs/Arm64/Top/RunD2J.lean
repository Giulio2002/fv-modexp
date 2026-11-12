import FvModexp.Proofs.Arm64.Top.RunDPc
import FvModexp.Proofs.Arm64.Top.RunD2Lem
import FvModexp.Proofs.Arm64.Top.RunL
import FvModexp.Proofs.Arm64.Top.RunBox
import FvModexp.Proofs.Arm64.Top.RunDSlot

/-!
# `Run` (arm64): the exponent operand from the join point `J2` (`setBytes` of the padded buffer) to `D2`

`J2` (`fn + 0x624`) is where the padded paths of `getData(input, baseLen, expLen)` meet: `X0` = the buffer `B` of
`expLen` bytes holding the call data from byte `96 + baseLen` on (zero past the end of the input), `X1 = X7 = expLen`,
`X2` = its capacity.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d2join (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 2 L2 b2 S2 → S2.pc = BitVec.ofNat 64 pcD2 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q)
    (U : State) (Lk : List (Nat × Nat)) (bk B : Nat) (hj : JoinD2 R b L c p len cp s ret Lk bk B U)
    (hpc : U.pc = BitVec.ofNat 64 pcJ2) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hz1, hz2, hz3,
    hl0, hl1, hl2, hnz, hr0, hr1, hr7, hr2, hB48, hBacc, hBH, hBW, hBv, hdS, hinS, hcS, hext, hbud, hinv, hLsS,
    hMF, hLF, hop0⟩ := hj
  subst hr0
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
  have hgS : U.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    gS_read hMF hga hgr
  have hwS : U.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : U.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hga
  have hwT : Outside SetBytes.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytes.wordT
  rw [h_t] at hwT hokS
  have hLS1 : ∀ r ∈ Lk, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hS := RunCallees.sbFixD impl hap R hmk bk Lk
  have hr7' : U.regs 7 = BitVec.ofNat 64 (hdrV s p len 1) := by
    apply BitVec.eq_of_toNat_eq; rw [hr7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr1' : U.regs 1 = BitVec.ofNat 64 (hdrV s p len 1) := by
    apply BitVec.eq_of_toNat_eq; rw [hr1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hokm : R.ok (cA "runtime.makeslice") [2641088, SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1)),
      makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1)))] := hokS _ (by simp [SetBytes.nW]; omega)
  have hMC0 : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1))) ≤ allocCost (8 * 132) := by
    have h1 : SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1)) ≤ 128 := by simp [SetBytes.nW]; omega
    have h3 : makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1))) ≤ 132 := by unfold makeCap; split <;> omega
    simp only [makeCost, allocCost]; omega
  have hMC : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1))) ≤ bk := by
    simp only [dCost, allocCost] at hbudD hMC0 hbud ⊢; omega
  have hRA := raSB impl hap 0x203710 (by decide)
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, hr7', hr1', hz1, hz2, hz3, natLive_zero] until [pcD2] calls [hP := hS]
  obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩,
    hd2⟩ := hP
  have bxBW := Box.mk hBW; have bxpw := Box.mk hpw; have bxcw := Box.mk hcw; have bxnz := Box.mk hnz
  have bxor := Box.mk hor2; have bxga := Box.mk hga
  clear hBW hpw hcw hnz hor2 hga
  have hspn' : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [← hsp]; exact hspn
  simp only [winA, hspn'] at hMF2
  have hLsL1 : LiveSep Lk (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by omega)
  have hstk : stk = 4800 := rfl
  have hLFS : LiveFrame U.mem s'.mem Lk [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
  refine hk _ L2 b2 (RelD.mk' hin0 (by janus_simp [hsp]) (by janus_simp [h28]) (by janus_simp [h29])
    (by janus_simp [h18]) (by janus_simp [hm1]) (by janus_simp [hm2]) (by janus_simp [hm3]) (by janus_simp [hm4])
    (by janus_simp [hm5]) (by janus_simp [hm6]) (by janus_simp [hs1]) (by janus_simp [hs2]) (by janus_simp [hs3])
    (by janus_simp [hs4]) (by janus_simp [hs5]) (by janus_simp [hs6]) hl0 hl1 hl2 bxnz.h (fun _ => ⟨by janus_simp [hs7], by janus_simp [hs8]⟩) ?_ ?_ (hext.trans hext2) ?_ ?_
    (hext2.liveSep hLsL1 hwrt) ?_ ?_ ?_ ?opsA) (by janus_simp)
  case opsA =>
    refine OpsApart.step' (p2 := p2) (c2 := c2) (opsApart_one _ _) (fun i hi => ?_) (fun i hi hc => by
        obtain rfl : i = 0 := by omega
        exact opDone_inRanges hop0 hc)
      (by janus_simp [hp2, opAt]) (by janus_simp [hc2, opAt]) (fun hc => ?_)
    · obtain rfl : i = 0 := by omega
      exact ⟨by janus_simp [opAt], by janus_simp [opAt]⟩
    · rcases bxor.h with ⟨-, h⟩ | ⟨-, h⟩
      · simp at h; omega
      · exact h
  · intro _; janus_simp [hs1] <;> omega
  · janus_callpre
  · exact bud_d2join hbud hMC0 hb2
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
    dsimp only
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact OpDone.transportS hop0 (k := 1) (by omega) (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp) (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame)
          (hext2.liveSep hLsL1 hwrt)) (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
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
      simp only [opV, opStart, opLen, if_neg (show (1 : Nat) ≠ 0 by decide), if_pos]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply beVal_padded
      intro j hj
      have hBW := bxBW.h
      rw [← hBv j hj, ← Memory.readLE_one, ← Memory.readLE_one, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

end FvModexp.Arm64.Run
