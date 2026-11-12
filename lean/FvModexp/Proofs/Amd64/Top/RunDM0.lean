import FvModexp.Proofs.Amd64.Top.RunDJDefs

/-! # `Run` (amd64): `C0` to `J0` — base operand, padded, `baseLen > 32`: `makeslice(uint8, h0, h0)`

As `RunDP0` up to the `JA` (`h0 > 32` taken): `AX = type:uint8`, `BX = CX = h0`, `makeslice` (call `fn + 0x661`,
return `fn + 0x666`), the registers reloaded from the slots, `SI` = the fresh zeroed buffer, `R10 = min(h0, DX)`: `J0`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dM0 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hbud : cstD 3 ≤ b)
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
    (hndir : len.toNat - 96 < hdrV s p len 0) (hbig : 32 < hdrV s p len 0)
    (hk : ∀ S2 bk dst e, JoinE R b L c p len cp s ret 0 L1 [(dst, e)] bk dst (p.toNat + inOff len) S2 →
      FreshDst R s (hdrV s p len 0) dst e → S2.rip = BitVec.ofNat 64 pcJ0 → (S2.regs 6).toNat = dst → (S2.regs 3).toNat = p.toNat + inOff len →
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
  have hc32 : (32 < hdrV s p len 0) = True := eq_true hbig
  have hsrc := src_facts0 p len (hdrV s p len 0) hp
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hmk' : MakesliceLiveContract64 (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
    MakesliceLiveContract64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmk
  have hmkP := hmk'.pos L1 b1
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [7231264, hdrV s p len 0, hdrV s p len 0] := by
    have := hokB _ hl0; rwa [h_u] at this
  have hU2 : S.mem.readLE 7231264 8 = 1 := by
    janus64_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hU3 : S.mem.readLE 7231272 8 = 0 := by
    janus64_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hut : Apart 7231264 16 ((s.regs 4).toNat - 4800) (4800 + 40) :=
    apart_of_data (x := 7231264) (l := 16) hd 0 (by decide) (by decide) hw
  unfold Apart at hut
  have hU1 : S.mem.accessible 7231264 16 false = true := by
    rw [hMF.accessible]; janus64_data hd; exact Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)
  have hAl : allocCost (hdrV s p len 0) ≤ allocCost 1024 := by unfold allocCost; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hl0) _
  have hBA : blockSize (hdrV s p len 0) true ≤ allocCost 1024 := Nat.le_trans (blockSize_le_allocCost _ true) hAl
  have hcst : 3 * makeCost 4 + allocCost 1024 ≤ cstE 0 := by unfold cstE; exact Nat.le_of_eq (by rw [Nat.zero_mul, Nat.add_zero])
  have hcb : cstE 0 ≤ b := Nat.le_trans (by unfold cstE cstD; exact Nat.add_le_add_left (Nat.le_trans (by unfold dCost; exact Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ (by decide))) _) hbud
  have hBS : blockSize (hdrV s p len 0) true ≤ b1 := by
    have := bud_alloc (r := 0) hbud1 (Nat.zero_le _) hcst hcb
    exact Nat.le_trans hBA (by have := Nat.sub_le_sub_left hcst b; unfold cstE at hcb; omega)
  have hLSm : ∀ r ∈ L1, Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
          ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
        [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
    intro r hr; have := hLsS r hr
    simp only [LiveSep, win, stk, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
    omega
  obtain ⟨hcf1, hcf2, hcf3, hcf4⟩ := frame_call_facts hal hg3 hga
  clear hpw hcw hcacc hc48 hcheld
  set_option janus.callRegions true in
  janus64_run [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, hr1', hI1, hI9, hc, hc32, hU2, hU3, toInt_ite, toNat_ite,
    BitVec.msb_eq_decide] until [pcJ0] calls [hmkP]
  rename_i ptr _ _ _ _ m _ _ hLFk hMFk hAp hIn hle hacc h8 _ hzk hsz hapW hinvk
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (win_len hb')
  have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 0) true)]) :=
    LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hMFm : MemFrame S.mem m (R.rt ++ win s stk 40) := by simp only [win, stk]; janus_frame
  have hacc' : s.mem.accessible ptr.toNat (hdrV s p len 0) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (Nat.add_le_add_left hsz _)
  refine hk _ (b1 - blockSize (hdrV s p len 0) true) ptr.toNat (ptr.toNat + blockSize (hdrV s p len 0) true)
    ⟨RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hl0 hl1 hl2 hnz
    ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩ ?_ ?_ (hext.trans hext') ?_ ?_
    (hext'.liveSep hLsS hwrt) ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ h => absurd h (Nat.not_lt_zero _)),
    fun _ => ?sl, ?zb, hsrc.1, hsrc.2.1, hsrc.2.2, ?d48, hacc', hext, liveSep_of_apartAll hAp,
    fun i h => absurd h (Nat.not_lt_zero i)⟩ ⟨Nat.add_le_add_left hsz _, by simpa using hIn,
      by simpa using fresh_out_win hb' hIn hout⟩ (by janus64_simp) (by janus64_simp) (by janus64_simp [hr3]) ?r10
      (by janus64_simp [hr1]) ?r2 (by janus64_simp [hr13])
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
  case h.refine_20 =>
    exact dataLoaded_frame64 hdS (by simp [hrg1]) hro hMFm (fun r hr _ => by
      simp only [win, stk, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact Janus.Arm64.Memory.accessible_mono _ hwS (Nat.le_refl _) (win_len hb'))
  case h.refine_21 => exact bud_alloc hbud1 hBA hcst hcb
  case h.refine_22 => exact hinvk
  case h.refine_23 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case h.refine_24 =>
    dsimp only
    exact hLF.trans ((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsS).trans hLFk (fun _ _ h => h))
      (fun _ _ h => hext.inRanges_old h)
  case sl =>
    janus64_simp [hr9]
    exact (Nat.min_eq_right (Nat.le_of_lt hndir)).symm
  case zb =>
    intro i hi
    simp only [opLen, ↓reduceIte] at hi
    simp only [Janus.Arm64.Memory.readLE_one, hzk i hi]; rfl
  case d48 => simp only [opLen, ↓reduceIte]; exact Nat.le_trans (Nat.add_le_add_left hsz _) hle
  case r10 => janus64_simp [hr9]; exact (Nat.min_eq_right (Nat.le_of_lt hndir)).symm
  case r2 => janus64_simp [hr9]; exact (Nat.min_eq_right (Nat.le_of_lt hndir)).symm

end FvModexp.Amd64.Run
