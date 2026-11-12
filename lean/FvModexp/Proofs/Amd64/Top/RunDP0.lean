import FvModexp.Proofs.Amd64.Top.RunDJDefs

/-! # `Run` (amd64): `C0` to `J0` — base operand, padded, `baseLen ≤ 32`: the zeroed stack buffer

At `C0` (`fn + 0x5c7`) the lengths are spilled and the base `big.Int` zeroed, `DX = min(h0, len - 96)` (`e - 512`);
`h0 > DX` (signed `JG`) and `h0 ≤ 32` (`JA` not taken): the 32-byte buffer `e - 392` is zeroed (two `MOVUPS X15`),
`SI = e - 392`, `R10 = min(h0, DX) = DX` (`CMOVG`): the join `J0` (`fn + 0x6a2`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dP0 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.rip = BitVec.ofNat 64 pcC0) (hTm : T.mem = S.mem) (hT4 : T.regs 4 = S.regs 4)
    (hT14 : T.regs 14 = S.regs 14) (hT5 : T.regs 5 = S.regs 5) (hTx : T.xmm 15 = S.xmm 15)
    (hTfs : T.fsBase = S.fsBase) (hTdf : T.df = S.df)
    (hl0 : hdrV s p len 0 ≤ 1024) (hl1 : hdrV s p len 1 ≤ 1024) (hl2 : hdrV s p len 2 ≤ 1024)
    (hnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (hr1 : (T.regs 1).toNat = hdrV s p len 0) (hr13 : (T.regs 13).toNat = hdrV s p len 1)
    (hr0 : (T.regs 0).toNat = hdrV s p len 2) (hr3 : (T.regs 3).toNat = p.toNat + (if 96 < len.toNat then 96 else 0))
    (hr7 : (T.regs 7).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0)) (hr9 : (T.regs 9).toNat = len.toNat - 96)
    (hndir : len.toNat - 96 < hdrV s p len 0) (hsm : hdrV s p len 0 ≤ 32)
    (hk : ∀ S2 bk, JoinE R b L c p len cp s ret 0 L1 [] bk (stkBuf s 0) (p.toNat + inOff len) S2 →
      S2.rip = BitVec.ofNat 64 pcJ0 →
      (S2.regs 6).toNat = (s.regs 4).toNat - 392 → (S2.regs 3).toNat = p.toNat + inOff len →
      (S2.regs 10).toNat = min (hdrV s p len 0) (len.toNat - 96) → (S2.regs 1).toNat = hdrV s p len 0 →
      (S2.regs 2).toNat = min (hdrV s p len 0) (len.toNat - 96) → (S2.regs 13).toNat = hdrV s p len 1 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have hin0 := hin
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, -, hdS, hinS, hcS, hext, hbud1, hinv, hLsS, hMF,
    hLF, -⟩ := hrel
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hpw hcw hMF
  simp only [win, Outside, and_true] at hpw hcw
  have hlen48 : len.toNat - 96 ≤ 2 ^ 48 := Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.le_add_left _ _) hp)
  have hI1 := toInt_small (T.regs 1) (by rw [hr1]; exact Nat.lt_of_le_of_lt hl0 (by decide))
  have hI9 := toInt_small (T.regs 9) (by rw [hr9]; exact Nat.lt_of_le_of_lt hlen48 (by decide))
  have hr1' : T.regs 1 = BitVec.ofNat 64 (hdrV s p len 0) := by
    apply BitVec.eq_of_toNat_eq; rw [hr1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hl0 (by decide))]
  have hc : ((T.regs 9).toNat < hdrV s p len 0) = True := by rw [hr9]; exact eq_true hndir
  have hc32 : (32 < hdrV s p len 0) = False := eq_false (Nat.not_lt.mpr hsm)
  have hsrc := src_facts0 p len (hdrV s p len 0) hp
  have hbuf := buf_in_win (n := 32) hb' (by decide) (by decide) (k := 392)
  have hbuf' := buf_in_win (n := 8) hb' (by decide) (by decide) (k := 512)
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  clear hpw hcw hga hcacc hc48 hcheld
  janus64_run [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, hr1', hI1, hI9, hc, hc32, toInt_ite, toNat_ite,
    BitVec.msb_eq_decide] until [pcJ0]
  have hLsL : LiveSep (L1 ++ []) (win s 4800 40) := by rw [List.append_nil]; exact hLsS
  refine hk _ b1 ⟨RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hl0 hl1 hl2 hnz
    ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩ ?_ ?_ (by rw [List.append_nil]; exact hext) ?_ ?_
    hLsL ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ h => absurd h (Nat.not_lt_zero _)),
    fun _ => ?sl, ?zb, hsrc.1, hsrc.2.1, hsrc.2.2, ?d48, ?dacc, fun _ _ => trivial,
    fun i h => absurd h (Nat.not_lt_zero i)⟩ (by janus64_simp) ?r6 (by janus64_simp [hr3]) ?r10 (by janus64_simp [hr1])
    ?r2 (by janus64_simp [hr13])
  all_goals try (janus64_simp [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, hr1, hr13, hr0, hr3, hr7, hr9, hc]; done)
  all_goals try (first | (dsimp only; rw [hTfs]; exact hfs; done) | (dsimp only; rw [hTdf]; exact hdf; done))
  case h.refine_19 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt]
    all_goals first
      | (janus64_simp; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod, hx15, hTx, hx0]; done)
      | janus64_simp [hTx, hx15, hx0]
  case h.refine_20 => janus64_callpre
  case h.refine_21 =>
    exact Nat.le_trans (Nat.sub_le_sub_left (by unfold cstE; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)) b) hbud1
  case h.refine_22 =>
    dsimp only
    rw [List.append_nil]
    repeat rw [view_writeLE_out (hout.of_sub (by omega) (by omega))]
    exact hinv
  case h.refine_23 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case h.refine_24 =>
    dsimp only
    exact hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsS) (fun _ _ h => hext.inRanges_old h)
  case sl =>
    janus64_simp [hr9]
    exact (Nat.min_eq_right (Nat.le_of_lt hndir)).symm
  case zb =>
    intro i hi
    simp only [opLen, stkBuf, ↓reduceIte, Nat.mul_zero, Nat.sub_zero] at hi ⊢
    rcases (Nat.lt_or_ge i 16) with h | h <;>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
      Nat.zero_div, Nat.zero_mod]
  case d48 => simp only [opLen, stkBuf, ↓reduceIte]; omega
  case dacc =>
    simp only [opLen, stkBuf, ↓reduceIte]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  case r10 => janus64_simp [hr9]; exact (Nat.min_eq_right (Nat.le_of_lt hndir)).symm
  case r2 => janus64_simp [hr9]; exact (Nat.min_eq_right (Nat.le_of_lt hndir)).symm

end FvModexp.Amd64.Run
