import FvModexp.Proofs.Amd64.Top.RunDJDefs
import FvModexp.Proofs.Amd64.Top.RunHMask

/-! # `Run` (amd64): `D1` to `pcE1` — exponent operand, direct slice (`expLen ≤ len(input[96:]) - start`)

At `D1` (`fn + 0x762`) `getData(input[96:], st, h1)` with `st = min(h0, len - 96)` (`e - 512`): `R9 = min(st + h1, len - 96)`
(`e - 520`, `CMOVB`), the slice-bounds `JA` (refuted: `st ≤ R9`), `R9 - st`, the re-slice mask `(-(cap - st)) >> 63 & st`
(`neg_asr63_and`); with `h1 ≤ R9 - st` (signed `JG` not taken) the buffer is the input slice itself; then
`e - 552 = h0 + h1` and the `setBytes` arguments (`z = nil` from the zeroed `big.Int`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dA1 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (Lk : List (Nat × Nat)) (bk : Nat) (hrel : RelD R b L c p len cp s ret 1 1 (cstD 1) Lk bk S)
    (hpc : S.rip = BitVec.ofNat 64 pcD1)
    (hdir : min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1 ≤ len.toNat - 96)
    (hE : ∀ S2, AtE R b L c p len cp s ret 1 pcE1 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  have hin0 := hin
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s3, s4, s5, s6, l0, l1, l2, lnz, hsl, hz,
    hdS, hinS, hcS, hext, hbk, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  obtain ⟨hsl1, hsl2⟩ := hsl.1 (Nat.le_refl _)
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz (by decide)
  simp only [opAt] at hz0 hz1 hz2 hz3
  have hgl := hg.load
  have hg3 := hg.below
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hb' ha hw hout hal
  simp only [stk] at hg3 hb' ha hw hout hpw hMF
  simp only [win, Outside, and_true] at hpw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  clear hga hcw hcacc hc48 hcheld hgr hLs htls
  have hst : min (hdrV s p len 0) (len.toNat - 96) ≤ len.toNat - 96 := Nat.min_le_right _ _
  have hst0 : min (hdrV s p len 0) (len.toNat - 96) ≤ hdrV s p len 0 := Nat.min_le_left _ _
  have hsteq : hdrV s p len 0 ≤ len.toNat - 96 → min (hdrV s p len 0) (len.toNat - 96) = hdrV s p len 0 :=
    Nat.min_eq_left
  have hdl48 : len.toNat - 96 < 2 ^ 48 := by omega
  have hcp63 : (BitVec.ofNat 64 (cp.toNat - inOff len)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hcpk : len.toNat - 96 ≤ cp.toNat - inOff len := by unfold inOff; split <;> omega
  have hJG : ((BitVec.ofNat 64 (hdrV s p len 1)).toInt < ↑(hdrV s p len 1)) = False := by
    rw [toInt_small _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp
  have hz1' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 160) 8 = 0 := by
    rw [show (s.regs 4).toNat - 160 = (s.regs 4).toNat - 136 - 32 * 1 + 8 by omega]; exact hz1
  have hz2' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 152) 8 = 0 := by
    rw [show (s.regs 4).toNat - 152 = (s.regs 4).toNat - 136 - 32 * 1 + 16 by omega]; exact hz2
  have hz3' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 144) 8 = 0 := by
    rw [show (s.regs 4).toNat - 144 = (s.regs 4).toNat - 136 - 32 * 1 + 24 by omega]; exact hz3
  generalize hstv : min (hdrV s p len 0) (len.toNat - 96) = st at hsl1 hsl2 hdir hst hst0 hsteq
  have hst63 : (BitVec.ofNat 64 st).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hcb : (len.toNat - 96 < st + hdrV s p len 1) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hsubB : BitVec.ofNat 64 (st + hdrV s p len 1) - BitVec.ofNat 64 st = BitVec.ofNat 64 (hdrV s p len 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmB := neg_asr63_andB _ _ hcp63 hst63
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show st < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show cp.toNat - inOff len < 2 ^ 64 by omega)] at hmB
  have bx := Box.mk <| And.intro hpw <| And.intro hinS <| And.intro hheld <| And.intro hpacc <| And.intro hp <|
    And.intro hlcp <| And.intro hcp48 <| And.intro hsteq hstv
  clear hpw hinS hheld hpacc hp hlcp hcp48 hsteq hstv
  janus64_run [hsp, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s4, s5, s6, hsl1, hsl2, hz1', hz2', hz3', hcb, hsubB, hJG, hmB,
    toInt_ite, toNat_ite, toInt_small, BitVec.msb_eq_decide] until [pcE1]
  obtain ⟨hpw, hinS, hheld, hpacc, hp, hlcp, hcp48, hsteq, hstv⟩ := bx.h
  have hLsL1 : LiveSep Lk (win s 4800 40) := hLsS
  refine hE _ ⟨Lk, bk, RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz ?_ ?_ ?_ hext ?_
    ?_ hLsS ?_ ?_ ?_ ?_, by janus64_simp, by janus64_simp, by janus64_simp, by janus64_simp, ?buf⟩
  case refine_19 =>
    refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩
    · rw [hstv]; janus64_simp [hsl1]
    · rw [hstv]; janus64_simp [hsl2]
    · janus64_simp
  case refine_20 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt]
    all_goals first
      | (janus64_simp [hz0]; done)
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; first | exact hz0 | exact hz1 | exact hz2 | exact hz3)
  case refine_21 => janus64_callpre
  case refine_22 => simp only [cstD, cstE] at hbk ⊢; omega
  case refine_23 =>
    dsimp only
    rw [view_writeLE_out (hout.of_sub (by omega) (by omega))]
    exact hinv
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => hext.inRanges_old h)
  case refine_26 =>
    intro j hj
    rcases (show j = 0 by omega) with rfl
    refine OpDone.transport (hop 0 (by omega)) ?_ ?_ ?_ ?_
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => h)
    all_goals (simp only [opAt]; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])
  case refine_27 =>
    refine OpsApart.transport hopA (fun i hi => ?_)
    rcases (show i = 0 by omega) with rfl
    simp only [opAt]
    exact ⟨Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)⟩
  case buf =>
    have hbp : (BitVec.ofNat 64 (if st < cp.toNat - inOff len then st else 0) + BitVec.ofNat 64 (p.toNat + inOff len)).toNat =
        p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; unfold inOff; split <;> split <;> omega
    have hite : (if st < cp.toNat - inOff len then BitVec.ofNat 64 st else 0#64) =
        BitVec.ofNat 64 (if st < cp.toNat - inOff len then st else 0) := by split <;> rfl
    have hrng : p.toNat ≤ p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0) ∧
        p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0) + hdrV s p len 1 ≤ p.toNat + len.toNat := by
      unfold inOff; split <;> split <;> omega
    have hoL : opLen s p len 1 = hdrV s p len 1 := rfl
    have hoS : opStart s p len 1 = hdrV s p len 0 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [hite, hbp]
    all_goals try janus64_simp [hite, hbp]
    · rfl
    · simp only [opV, hoS, hoL]
      rcases Nat.eq_zero_or_pos (hdrV s p len 1) with h1 | h1
      · rw [h1]; rfl
      · have h96 : 96 < len.toNat := by omega
        have hh0 : hdrV s p len 0 ≤ len.toNat - 96 := by
          rcases Nat.le_total (hdrV s p len 0) (len.toNat - 96) with h | h
          · exact h
          · have : st = len.toNat - 96 := by rw [← hstv]; exact Nat.min_eq_right h
            omega
        have hst' : st = hdrV s p len 0 := by rw [← hstv]; exact Nat.min_eq_left hh0
        rw [padBE_inside _ _ _ _ _ (by omega)]
        refine beVal_of_reads' (by unfold inOff; rw [if_pos h96, if_pos (by omega)]; omega) rfl fun i hi => ?_
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hinS _ _ (by omega) (by omega)
    · exact Janus.Arm64.Memory.accessible_mono _ hpacc hrng.1 hrng.2
    · omega
    · exact hext.held (hheld.sub hrng.1 hrng.2)
    · first | omega | (simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega)
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf; done) | (simp only [hfs]; done) | (simp only [hdf]; done))

end FvModexp.Amd64.Run
