import FvModexp.Proofs.Amd64.Top.RunDKDefs

/-! # `Run` (amd64): `D1` to `pcE2` — exponent operand, direct slice (`expLen ≤ len(input[96:]) - start`)

At `D1` (`fn + 0x762`) `getData(input[96:], st, h1)` with `st = min(h0, len - 96)` (`e - 512`): `R9 = min(st + h1, len - 96)`
(`e - 520`, `CMOVB`), the slice-bounds `JA` (refuted: `st ≤ R9`), `R9 - st`, the re-slice mask `(-(cap - st)) >> 63 & st`
(`neg_asr63_and`); with `h1 ≤ R9 - st` (signed `JG` not taken) the buffer is the input slice itself; then
`e - 552 = h0 + h1` and the `setBytes` arguments (`z = nil` from the zeroed `big.Int`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dA2 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (Lk : List (Nat × Nat)) (bk : Nat) (hrel : RelD R b L c p len cp s ret 2 2 (cstD 2) Lk bk S)
    (hpc : S.rip = BitVec.ofNat 64 pcD2)
    (hdir : min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) + hdrV s p len 2 ≤ len.toNat - 96)
    (hE : ∀ S2, AtE R b L c p len cp s ret 2 pcE2 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  have hin0 := hin
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s3, s4, s5, s6, l0, l1, l2, lnz, hsl, hz,
    hdS, hinS, hcS, hext, hbk, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  obtain ⟨hsl1, hsl2⟩ := hsl.1 (by decide)
  have hsl3 := hsl.2 (Nat.le_refl _)
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
  have hst : min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) ≤ len.toNat - 96 := Nat.min_le_right _ _
  have hdl48 : len.toNat - 96 < 2 ^ 48 := by omega
  have hcp63 : (BitVec.ofNat 64 (cp.toNat - inOff len)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hJG : ((BitVec.ofNat 64 (hdrV s p len 2)).toInt < ↑(hdrV s p len 2)) = False := by
    rw [toInt_small _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp
  have hz1' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 192) 8 = 0 := by
    rw [show (s.regs 4).toNat - 192 = (s.regs 4).toNat - 136 - 32 * 2 + 8 by omega]; exact hz1
  have hz2' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 184) 8 = 0 := by
    rw [show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 136 - 32 * 2 + 16 by omega]; exact hz2
  have hz3' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 176) 8 = 0 := by
    rw [show (s.regs 4).toNat - 176 = (s.regs 4).toNat - 136 - 32 * 2 + 24 by omega]; exact hz3
  have hR9 : (if len.toNat - 96 < hdrV s p len 0 + hdrV s p len 1 then BitVec.ofNat 64 (len.toNat - 96)
      else BitVec.ofNat 64 (hdrV s p len 0 + hdrV s p len 1)) =
      BitVec.ofNat 64 (min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96)) := by
    split <;> rename_i h
    · rw [Nat.min_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_left (Nat.le_of_not_lt h)]
  generalize hstv : min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) = st at hdir hst hR9
  have hst63 : (BitVec.ofNat 64 st).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hadd : BitVec.ofNat 64 (hdrV s p len 2) + BitVec.ofNat 64 st = BitVec.ofNat 64 (st + hdrV s p len 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcb : (len.toNat - 96 < st + hdrV s p len 2) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hsubB : BitVec.ofNat 64 (st + hdrV s p len 2) - BitVec.ofNat 64 st = BitVec.ofNat 64 (hdrV s p len 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmB := neg_asr63_andB' _ _ hcp63 hst63
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show st < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show cp.toNat - inOff len < 2 ^ 64 by omega)] at hmB
  have hsrc := opsrc_dir (pp := p.toNat) (k := inOff len) hstv.symm rfl hlcp hdir
  have bx := Box.mk <| And.intro hpw <| And.intro hinS <| And.intro hheld <| And.intro hpacc <| And.intro hp <|
    And.intro hlcp <| And.intro hcp48 hstv
  clear hpw hinS hheld hpacc hp hlcp hcp48 hstv
  janus64_run [hsp, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s3, s4, s5, s6, hsl1, hsl2, hsl3, hz1', hz2', hz3', hR9, hadd,
    hcb, hsubB, hJG, hmB, toInt_ite, toNat_ite, toInt_small, BitVec.msb_eq_decide] until [pcE2]
  obtain ⟨hpw, hinS, hheld, hpacc, hp, hlcp, hcp48, hstv⟩ := bx.h
  have hoL : opLen s p len 2 = hdrV s p len 2 := rfl
  have hoS : opStart s p len 2 = hdrV s p len 0 + hdrV s p len 1 := rfl
  have hite : (if st < cp.toNat - inOff len then BitVec.ofNat 64 st else 0#64) =
      BitVec.ofNat 64 (if st < cp.toNat - inOff len then st else 0) := by split <;> rfl
  have hbp : (BitVec.ofNat 64 (if st < cp.toNat - inOff len then st else 0) + BitVec.ofNat 64 (p.toNat + inOff len)).toNat =
      p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show (if st < cp.toNat - inOff len then st else 0) < 2 ^ 64 by split <;> omega),
      Nat.mod_eq_of_lt (show p.toNat + inOff len < 2 ^ 64 by unfold inOff; split <;> omega)]
    rw [Nat.mod_eq_of_lt (show (if st < cp.toNat - inOff len then st else 0) + (p.toNat + inOff len) < 2 ^ 64 by
      unfold inOff; split <;> split <;> omega)]
    omega
  obtain ⟨hs1, hs2, hs3⟩ := hsrc
  refine hE _ ⟨Lk, bk, RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz
    ⟨fun _ => hsl.1 (by decide), fun _ => hsl.2 (by decide)⟩ ?_ ?_ hext ?_ hinv hLsS hMF hLF hop hopA,
    by janus64_simp, by janus64_simp, by janus64_simp, by janus64_simp, ?buf⟩
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf; done) | (simp only [hfs]; done) | (simp only [hdf]; done))
  case refine_19 =>
    intro _
    exact ⟨hz0, hz1, hz2, hz3⟩
  case refine_20 => janus64_callpre
  case refine_21 => simp only [cstD, cstE] at hbk ⊢; omega
  case buf =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hmB, hite, hbp]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
    · simp only [opV, hoS, hoL]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rcases Nat.eq_zero_or_pos (hdrV s p len 2) with h1 | h1
      · rw [h1]; rfl
      · rw [padBE_inside _ _ _ _ _ (by omega)]
        refine beVal_of_reads' (by rw [hs3 h1]; omega) rfl fun i hi => ?_

        exact hinS _ _ (by omega) (by omega)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact Janus.Arm64.Memory.accessible_mono _ hpacc hs1 hs2
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hext.held (hheld.sub hs1 hs2)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      first | omega | (simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega)

end FvModexp.Amd64.Run
