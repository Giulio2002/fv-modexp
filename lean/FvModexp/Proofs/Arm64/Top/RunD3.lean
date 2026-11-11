import FvModexp.Proofs.Arm64.Top.RunD2
import FvModexp.Proofs.Arm64.Top.RunD2Lem

/-! # `Run` (arm64): `D1` to `D2` — the exponent operand (`getData(input, baseLen, expLen)`, patched `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcD3 : Nat := segAddr Extracted.program fn + 0x760

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem d3x (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 2 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcD2)
    (hdir0 : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2 ≤ len.toNat - 96)
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 L2 b2 S2 →
      (S2.regs 0).toNat = S2.mem.readLE (s.sp.toNat - 192) 8 → (S2.regs 1).toNat = S2.mem.readLE (s.sp.toNat - 184) 8 →
      S2.pc = BitVec.ofNat 64 pcD3 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, hk1, hk2,
    hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF, hop⟩ := hrel
  obtain ⟨hk1a, hk1b⟩ := hk1 (by omega)
  have hk2a := hk2 (by omega)
  have hS1n : (if len.toNat - 96 < hdrV s p len 1 + hdrV s p len 0 then len.toNat - 96 else hdrV s p len 1 + hdrV s p len 0) =
      min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) := by split <;> omega
  have hS1 : (if len.toNat - 96 < hdrV s p len 1 + hdrV s p len 0 then BitVec.ofNat 64 (len.toNat - 96)
      else BitVec.ofNat 64 (hdrV s p len 1 + hdrV s p len 0)) = BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) := by
    split <;> (congr 1; omega)
  have hadd : BitVec.ofNat 64 (hdrV s p len 2) + BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) := bv_add_of_lt _ _ (by omega)
  have hmod : (hdrV s p len 2 + min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) % 18446744073709551616 = min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
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
  have hMC0 : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2))) ≤ allocCost (8 * 132) := by
    have h1 : SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2)) ≤ 128 := by simp [SetBytes.nW]; omega
    have h3 : makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2))) ≤ 132 := by unfold makeCap; split <;> omega
    simp only [makeCost, allocCost]; omega
  have hMC : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2))) ≤ b1 := by
    simp only [dCost, allocCost] at hbudD hbud hMC0 ⊢; omega
  have hokm : R.ok (cA "runtime.makeslice") [2641088, SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2)),
      makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2)))] := hokS _ (by simp [SetBytes.nW]; omega)
  by_cases hdir : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2 ≤ len.toNat - 96
  · have hc : (len.toNat - 96 < min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) = False := by simp; omega
    have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
    obtain ⟨off, hoffd⟩ : ∃ off, inOff len = off := ⟨_, rfl⟩
    have hoffc : (96 < len.toNat ∧ off = 96) ∨ (len.toNat ≤ 96 ∧ off = 0) := by
      subst hoffd; simp only [inOff]; split <;> omega
    rw [hoffd] at hs5 hs6
    have hcap : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) ≤ cp.toNat - off := by omega
    obtain ⟨mN, hmNd⟩ : ∃ mN, (if min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) < cp.toNat - off then
        min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) else 0) = mN := ⟨_, rfl⟩
    have hmN : mN ≤ min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) ∧ (hdrV s p len 2 = 0 ∨ mN = min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) := by
      subst hmNd; split <;> omega
    have hmask : (BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) &&&
        (BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) - BitVec.ofNat 64 (cp.toNat - off)).sshiftRight 63) =
        BitVec.ofNat 64 mN := by
      apply BitVec.eq_of_toNat_eq
      rw [sliceMask_le _ _ hcap (by omega), hmNd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsub : BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) -
        BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) = BitVec.ofNat 64 (hdrV s p len 2) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) (by omega),
        Nat.mod_eq_of_lt (a := min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) (by omega),
        Nat.mod_eq_of_lt (a := hdrV s p len 2) (by omega)]; omega
    have hcsub : BitVec.ofNat 64 (cp.toNat - off) - BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) =
        BitVec.ofNat 64 (cp.toNat - off - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) (by omega),
        Nat.mod_eq_of_lt (a := cp.toNat - off) (by omega),
        Nat.mod_eq_of_lt (a := cp.toNat - off - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) (by omega)]; omega
    have hsrc : BitVec.ofNat 64 mN + BitVec.ofNat 64 (p.toNat + off) = BitVec.ofNat 64 (p.toNat + off + mN) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := mN) (by omega), Nat.mod_eq_of_lt (a := p.toNat + off) (by omega),
        Nat.mod_eq_of_lt (a := p.toNat + off + mN) (by omega)]; omega
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hk1a, hk1b, hk2a, hS1, hS1n, hadd, hmod, hc, hIe, hmask, hsub, hcsub, hsrc,
      toInt_ite, toNat_ite, toInt_small] until [segAddr Extracted.program fn + 0x750]
    have hsrcL : p.toNat + off + mN + hdrV s p len 2 ≤ p.toNat + len.toNat := by omega
    have hH : InRanges (p.toNat + off + mN) (hdrV s p len 2) L1 ∨ Outside (p.toNat + off + mN) (hdrV s p len 2) R.rt :=
      hext.held (hheld.sub (by omega) hsrcL)
    have hB48 : p.toNat + off + mN + hdrV s p len 2 ≤ 2 ^ 48 := by omega
    have hAcc : s.mem.accessible (p.toNat + off + mN) (hdrV s p len 2) false = true :=
      Memory.accessible_mono _ hpacc (by omega) hsrcL
    have hW : p.toNat + off + mN + hdrV s p len 2 ≤ BitVec.toNat s.sp - 624 - 4160 ∨
        BitVec.toNat s.sp - 624 + 48 ≤ p.toNat + off + mN := by omega
    janus_data hdS
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, natLive_zero] until [pcD3] calls [hP := hS]
    obtain ⟨⟨-, p2, n2, c2, hp2, hn2, hc2, hv2, hnorm2, hnc2, hnw2, L2, b2, hext2, hb2, hinv2, hlive2, hor2, hMF2, hLF2⟩,
      hd2⟩ := hP
    have hspn' : (s.sp - 624#64).toNat = s.sp.toNat - 624 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [winA, hspn'] at hMF2
    have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
    have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (Nat.le_refl _) (by omega)
    have hstk : stk = 4800 := rfl
    have hLFS : LiveFrame S.mem s'.mem L1 [] :=
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.of_empty hLF2 []) (fun _ _ h => h)
    refine hk _ L2 b2 (RelD.mk' hin0 (by janus_simp [hsp]) (by janus_simp [h28]) (by janus_simp [h29])
      (by janus_simp [h18]) (by janus_simp [hm1]) (by janus_simp [hm2]) (by janus_simp [hm3]) (by janus_simp [hm4])
      (by janus_simp [hm5]) (by janus_simp [hm6]) (by janus_simp [hs1]) (by janus_simp [hs2]) (by janus_simp [hs3])
      (by janus_simp [hs4]) (by janus_simp [hs5, hoffd]) (by janus_simp [hs6, hoffd]) hl0 hl1 hl2 hnz
      (fun _ => ⟨by janus_simp [hk1a], by janus_simp [hk1b]⟩) (fun _ => by janus_simp [hk2a]) ?_ (hext.trans hext2) ?_ ?_
      (hext2.liveSep hLsL1 hwrt) ?_ ?_ ?_) (by janus_simp [hp2]) (by janus_simp [hn2]) (by janus_simp)
    · janus_callpre
    · have hD : allocCost (8 * 132) ≤ dCost := Nat.le_add_left _ _
      omega
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
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact OpDone.transport (hop 0 (by omega)) (by janus_simp [opAt]) (by janus_simp [opAt]) (by janus_simp [opAt])
          (by janus_simp [opAt]) (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame)
            (hext2.liveSep hLsL1 hwrt)) (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
      · exact OpDone.transport (hop 1 (by omega)) (by janus_simp [opAt]) (by janus_simp [opAt]) (by janus_simp [opAt])
          (by janus_simp [opAt]) (hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame)
            (hext2.liveSep hLsL1 hwrt)) (fun _ _ h => hext2.inRanges_old h)) (fun _ _ h => hext2.inRanges_old h)
      refine opDone_of (m := s'.mem) ?rd (hacc := fun a n w => by
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
        rcases hor2 with ⟨-, h⟩ | ⟨h, -⟩
        · simp at h; omega
        · exact h
      case v =>
        rw [hv2]
        simp only [opV, opStart, opLen, if_neg (show (2 : Nat) ≠ 0 by decide), if_neg (show (2 : Nat) ≠ 1 by decide)]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        by_cases h0 : hdrV s p len 2 = 0
        · rw [h0]; rfl
        · have hmE : mN = min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) := by omega
          have h96 : 96 < len.toNat := by omega
          have hoff : off = 96 := by omega
          have hmin : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) = hdrV s p len 0 + hdrV s p len 1 := by omega
          rw [hmE, hoff, hmin, padBE_inside _ _ _ _ _ (by omega),
            show p.toNat + (96 + (hdrV s p len 0 + hdrV s p len 1)) = p.toNat + 96 + (hdrV s p len 0 + hdrV s p len 1) by omega]
          apply beVal_of_reads
          intro i hi
          repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
          exact hinS _ _ (by omega) (by omega)
  · exact absurd hdir0 hdir

end FvModexp.Arm64.Run
