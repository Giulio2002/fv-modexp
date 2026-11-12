import FvModexp.Proofs.Amd64.Top.RunDKDefs

/-! # `Run` (amd64): `D1` to `J1` — modulus operand, padded, `expLen > 32`: a fresh `makeslice` buffer

As `dP1` up to `h1 > 32` (`JA` taken): `e - 560 = end - st`, `e - 224 = src` are spilled, `makeslice(uint8, h1, h1)`
(`fn + 0x806`, returns at `fn + 0x80b`), the registers are reloaded, `R11 = min(h1, end - st) = end - st` (`CMOVG`):
the join `J1` (`fn + 0x840`) with `AX` = the fresh buffer. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dM2 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hbud : cstD 3 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (Lk : List (Nat × Nat)) (bk : Nat) (hrel : RelD R b L c p len cp s ret 2 2 (cstD 2) Lk bk S)
    (hpc : S.rip = BitVec.ofNat 64 pcD2)
    (hndir : len.toNat - 96 < min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) + hdrV s p len 2) (hbig : 32 < hdrV s p len 2)
    (hk : ∀ S2 bk' dst e src, JoinE R b L c p len cp s ret 2 Lk [(dst, e)] bk' dst src S2 →
      FreshDst R s (hdrV s p len 2) dst e → S2.rip = BitVec.ofNat 64 pcJ2 →
      (S2.regs 0).toNat = dst → (S2.regs 3).toNat = src →
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
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hpw hMF
  simp only [win, Outside, and_true] at hpw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  clear hcw hcacc hc48 hcheld
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
  have hc32 : (32 < hdrV s p len 2) = True := eq_true hbig
  have hmB := neg_asr63_andB' _ _ hcp63 hst63
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show st < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show cp.toNat - inOff len < 2 ^ 64 by omega)] at hmB
  have hsrc := opsrc (pp := p.toNat) (h := hdrV s p len 2) hstv.symm rfl hlcp
  rw [Nat.min_eq_right (Nat.le_of_lt hndir), opavail_pad hstv.symm hndir] at hsrc
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hmk' : MakesliceLiveContract64 (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
    MakesliceLiveContract64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmk
  have hmkP := hmk'.pos Lk bk
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [7231264, hdrV s p len 2, hdrV s p len 2] := by
    have := hokB _ l2; rwa [h_u] at this
  obtain ⟨hU2, hU3⟩ := uint8_words hdS
  have hut : Apart 7231264 16 ((s.regs 4).toNat - 4800) (4800 + 40) :=
    apart_of_data (x := 7231264) (l := 16) hd 0 (by decide) (by decide) hw
  unfold Apart at hut
  have hU1 : S.mem.accessible 7231264 16 false = true := by rw [hMF.accessible]; exact uint8_acc hd
  have hAl : allocCost (hdrV s p len 2) ≤ allocCost 1024 := by unfold allocCost; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ l2) _
  have hBA : blockSize (hdrV s p len 2) true ≤ allocCost 1024 := Nat.le_trans (blockSize_le_allocCost _ true) hAl
  have hcst : cstD 2 + allocCost 1024 ≤ cstE 2 := Nat.le_refl _
  have hcb' : cstE 2 ≤ b := Nat.le_trans (by simp only [cstE, cstD, dCost]; omega) hbud
  have hBS : blockSize (hdrV s p len 2) true ≤ bk := by
    have := bud_alloc (r := 0) hbk (Nat.zero_le _) hcst hcb'
    simp only [cstE, cstD] at hcb' hbk; omega
  have hLSm : ∀ r ∈ Lk, Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
          ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
        [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
    intro r hr; have := hLsS r hr
    simp only [LiveSep, win, stk, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
    omega
  obtain ⟨hcf1, hcf2, hcf3, hcf4⟩ := frame_call_facts hal hg3 hga
  rw [hx0] at hx15
  have bx := Box.mk <| And.intro hpw <| And.intro hinS <| And.intro hheld <| And.intro hpacc <| And.intro hp <|
    And.intro hlcp <| And.intro hcp48 <| And.intro hstv <| And.intro hsrc <| And.intro hop hopA
  clear hpw hinS hheld hpacc hp hlcp hcp48 hstv hsrc hop hopA
  set_option janus.callRegions true in
  janus64_run [hsp, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s4, s5, s6, s3, hsl1, hsl2, hsl3, hz1', hz2', hz3', hR9, hadd, hcb, hsubB, hJG, hmB,
    hc32, hx15, hU2, hU3, toInt_ite, toNat_ite, toInt_small, BitVec.msb_eq_decide] until [pcJ2] calls [hmkP]
  rename_i ptr _ _ _ _ m _ _ hLFk hMFk hAp hIn hle hacc h8 _ hzk hsz hapW hinvk
  obtain ⟨hpw, hinS, hheld, hpacc, hp, hlcp, hcp48, hstv, hsrc, hop, hopA⟩ := bx.h
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (win_len hb')
  have hext' : LiveExt R Lk (Lk ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) :=
    LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hMFm : MemFrame S.mem m (R.rt ++ win s stk 40) := by simp only [win, stk]; janus_frame
  have hLFS : LiveFrame S.mem m Lk [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsS).trans hLFk (fun _ _ h => h)
  have hacc' : s.mem.accessible ptr.toNat (hdrV s p len 2) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (Nat.add_le_add_left hsz _)
  have hoL : opLen s p len 2 = hdrV s p len 2 := rfl
  have hoA : opAvail s p len 2 = min (hdrV s p len 2) (len.toNat - 96 - (hdrV s p len 0 + hdrV s p len 1)) := rfl
  have hoS : opStart s p len 2 = hdrV s p len 0 + hdrV s p len 1 := rfl
  have hbp : (((if st < cp.toNat - inOff len then st else 0) + (p.toNat + inOff len) % 18446744073709551616) %
      18446744073709551616) = p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0) := by
    clear hinvk hMFk hLFk hMFm hLFS hext' hinv hMF hLF hop hopA hLSm hinS
    unfold inOff; split <;> split <;> omega
  refine hk _ (bk - blockSize (hdrV s p len 2) true) ptr.toNat (ptr.toNat + blockSize (hdrV s p len 2) true)
    (p.toNat + inOff len + (if st < cp.toNat - inOff len then st else 0))
    ⟨RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz ?_ ?_ ?_ (hext.trans hext') ?_ ?_
    (hext'.liveSep hLsS hwrt) ?_ ?_ ?_ ?_,
    fun h => absurd h (by decide), ?zb, hsrc.1, hsrc.2.1, hsrc.2.2.1, ?d48, by rw [hoL]; exact hacc', hext,
    liveSep_of_apartAll hAp, ?op⟩ ⟨Nat.add_le_add_left hsz _, by simpa using hIn, by simpa using fresh_out_win hb' hIn hout⟩
    (by janus64_simp) (by janus64_simp) ?r3 ?r11 (by janus64_simp)
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf; done) | (simp only [hfs]; done) | (simp only [hdf]; done))
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
  case refine_21 =>
    exact dataLoaded_frame64 hdS (by simp [hrg1]) hro hMFm (fun r hr _ => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact Janus.Arm64.Memory.accessible_mono _ hwS (Nat.le_refl _) (win_len hb'))
  case refine_22 => exact bud_alloc hbk hBA hcst hcb'
  case refine_23 => exact hinvk
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
  case refine_26 =>
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
    refine OpDone.transport (hop _ (by omega)) ?_ ?_ ?_ ?_ hLFS (fun _ _ h => hext'.inRanges_old h)
    all_goals (simp only [opAt]; janus64_simp)
  case refine_27 =>
    refine OpsApart.transport hopA (fun i hi => ?_)
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    simp only [opAt] <;>
    exact ⟨by janus64_simp, by janus64_simp⟩
  case op =>
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
    refine OpDone.transport (hop _ (by omega)) ?_ ?_ ?_ ?_ hLFS (fun _ _ h => h)
    all_goals (simp only [opAt]; janus64_simp)
  case zb =>
    intro i hi
    rw [hoL] at hi
    simp only [Janus.Arm64.Memory.readLE_one, hzk i hi]; rfl
  case d48 => rw [hoL]; exact Nat.le_trans (Nat.add_le_add_left hsz _) hle
  case r3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbp]
  case r11 =>
    simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
    rw [hoA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), opavail_pad hstv.symm hndir]

end FvModexp.Amd64.Run
