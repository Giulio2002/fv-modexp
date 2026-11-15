import FvModexp.Proofs.Amd64.Top.RunDKDefs
import FvModexp.Proofs.Amd64.Top.RunDSlot

/-! # `Run` (amd64): `D1` to `J1` — modulus operand, padded, `expLen ≤ 32`: the zeroed stack buffer

As `dA1` up to the signed `JG` (taken: `h1 > end - st`), then `h1 ≤ 32` (`JA` not taken): the 32-byte buffer `e - 456`
is zeroed (two `MOVUPS X15`), `AX = e - 456`, `R11 = min(h1, end - st) = end - st` (`CMOVG`): the join `J1`
(`fn + 0x840`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dP2 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (Lk : List (Nat × Nat)) (bk : Nat) (hrel : RelD R b L c p len cp s ret 2 2 (cstD 2) Lk bk S)
    (hpc : S.rip = BitVec.ofNat 64 pcD2)
    (hndir : len.toNat - 96 < min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) + hdrV s p len 2) (hsm : hdrV s p len 2 ≤ 32)
    (hk : ∀ S2 bk' src, JoinE R b L c p len cp s ret 2 Lk [] bk' (stkBuf s 2) src S2 → S2.rip = BitVec.ofNat 64 pcJ2 →
      (S2.regs 0).toNat = (s.regs 4).toNat - 456 → (S2.regs 3).toNat = src →
      (S2.regs 2).toNat = opAvail s p len 2 → (S2.regs 1).toNat = hdrV s p len 2 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
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
  have hcpk : len.toNat - 96 ≤ cp.toNat - inOff len := by unfold inOff; split <;> omega
  have hz1' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 192) 8 = 0 := by
    rw [show (s.regs 4).toNat - 192 = (s.regs 4).toNat - 136 - 32 * 2 + 8 by omega]; exact hz1
  have hz2' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 184) 8 = 0 := by
    rw [show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 136 - 32 * 2 + 16 by omega]; exact hz2
  have hz3' : Arm64.Memory.readLE S.mem ((s.regs 4).toNat - 176) 8 = 0 := by
    rw [show (s.regs 4).toNat - 176 = (s.regs 4).toNat - 136 - 32 * 2 + 24 by omega]; exact hz3
  have hR9 : (if len.toNat - 96 < hdrV s p len 0 + hdrV s p len 1 then BitVec.ofNat 64 (len.toNat - 96)
      else BitVec.ofNat 64 (hdrV s p len 0 + hdrV s p len 1)) = BitVec.ofNat 64 (min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96)) := by
    split <;> rename_i h
    · rw [Nat.min_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_left (Nat.le_of_not_lt h)]
  generalize hstv : min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) = st at hndir hst hR9
  have hadd : BitVec.ofNat 64 (hdrV s p len 2) + BitVec.ofNat 64 st = BitVec.ofNat 64 (st + hdrV s p len 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hst63 : (BitVec.ofNat 64 st).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hcb : (len.toNat - 96 < st + hdrV s p len 2) = True := eq_true hndir
  have hsubB : BitVec.ofNat 64 (len.toNat - 96) - BitVec.ofNat 64 st = BitVec.ofNat 64 (len.toNat - 96 - st) :=
    ofNat_sub64 hst (by omega)
  have hJG : ((BitVec.ofNat 64 (len.toNat - 96 - st)).toInt < ↑(hdrV s p len 2)) = True := by
    rw [toInt_small _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
  have hc32 : (32 < hdrV s p len 2) = False := eq_false (Nat.not_lt.mpr hsm)
  have hmB := neg_asr63_andB' _ _ hcp63 hst63
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show st < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show cp.toNat - inOff len < 2 ^ 64 by omega)] at hmB
  have hsrc := opsrc (pp := p.toNat) (h := hdrV s p len 2) hstv.symm rfl hlcp
  rw [Nat.min_eq_right (Nat.le_of_lt hndir), opavail_pad hstv.symm hndir] at hsrc
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  rw [hx0] at hx15
  have hpm := pin_mod (p := p.toNat) len hp
  have bx := Box.mk <| And.intro hpw <| And.intro hinS <| And.intro hheld <| And.intro hpacc <| And.intro hp <|
    And.intro hlcp <| And.intro hcp48 <| hstv
  clear hpw hinS hheld hpacc hp hlcp hcp48 hstv
  janus64_run [hpm, hsp, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s4, s5, s6, s3, hsl1, hsl2, hsl3, hz1', hz2', hz3', hR9, hadd, hcb, hsubB, hJG, hmB,
    hc32, hx15, toInt_ite, toNat_ite, toInt_small, BitVec.msb_eq_decide] until [pcJ2]
  obtain ⟨hpw, hinS, hheld, hpacc, hp, hlcp, hcp48, hstv⟩ := bx.h
  have hLsL1 : LiveSep Lk (win s 4800 40) := hLsS
  have hLsL : LiveSep (Lk ++ []) (win s 4800 40) := by rw [List.append_nil]; exact hLsS
  have hoL : opLen s p len 2 = hdrV s p len 2 := rfl
  have hoA : opAvail s p len 2 = min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1)) := rfl
  have hoS : opStart s p len 2 = hdrV s p len 0 + hdrV s p len 1 := rfl
  have hite : (if st < cp.toNat - inOff len then BitVec.ofNat 64 st else 0#64) =
      BitVec.ofNat 64 (if st < cp.toNat - inOff len then st else 0) := by split <;> rfl
  have hbp : (BitVec.ofNat 64 (if st < cp.toNat - inOff len then st else 0) + BitVec.ofNat 64 (p.toNat + inOff len)).toNat =
      p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; unfold inOff; split <;> split <;> omega
  refine hk _ bk (p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0))
    ⟨RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz ?_ ?_ ?_
    (by rw [List.append_nil]; exact hext) ?_ ?_ hLsL ?_ ?_ ?_ ?_,
    fun h => absurd h (by decide), ?zb, hsrc.1, hsrc.2.1, ?s3, ?d48, ?dacc, hext, fun _ _ => trivial, ?op⟩
    (by janus64_simp) ?r0 ?r3 ?r11 ?r1
  case refine_19 =>
    refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩
    · janus64_simp [hsl1]
    · janus64_simp [hsl2]
    · janus64_simp [hsl3]
  case refine_20 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt]
    all_goals janus64_simp [hz0, hz1, hz2, hz3]
  case refine_21 => janus64_callpre
  case refine_22 => simp only [cstD, cstE] at hbk ⊢; omega
  case refine_23 =>
    dsimp only
    rw [List.append_nil, view_writeLE_out (hout.of_sub (by omega) (by omega)),
      view_writeLE_out (hout.of_sub (by omega) (by omega))]
    exact hinv
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1)
      (fun _ _ h => by first | (rw [List.append_nil]; exact hext.inRanges_old h) | exact hext.inRanges_old h)
  case refine_26 =>
    intro j hj
    refine OpDone.transportS (hop _ (by omega)) (k := 2) hj ?_
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => by first | (rw [List.append_nil]; exact h) | exact h)
    intro a n h1 h2; simp only [opAt] at h1 h2; janus64_simp
  case refine_27 =>
    refine OpsApart.transportS hopA ?_
    intro a n h1 h2; simp only [opAt] at h1 h2; janus64_simp
  case op =>
    intro j hj
    refine OpDone.transportS (hop _ (by omega)) (k := 2) hj ?_
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => h)
    intro a n h1 h2; simp only [opAt] at h1 h2; janus64_simp
  case zb =>
    intro i hi
    rw [hoL] at hi
    simp only [stkBuf]
    rcases (Nat.lt_or_ge i 16) with h | h <;>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
      Nat.zero_div, Nat.zero_mod]
  case s3 => rw [hoA, hoS]; exact hsrc.2.2.1
  case d48 => simp only [hoL, stkBuf]; omega
  case dacc =>
    simp only [hoL, stkBuf]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  case r3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [hite, hbp]
  case r11 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [hoA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), opavail_pad hstv.symm hndir]
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf; done) | (simp only [hfs]; done) | (simp only [hdf]; done))

end FvModexp.Amd64.Run
