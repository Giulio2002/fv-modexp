import FvModexp.Proofs.Amd64.Top.RunCDefs
import FvModexp.Proofs.Common.GenReg
import FvModexp.Proofs.Amd64.Top.RunU8

/-! # `Run` (amd64): `D3` to `C2` or the return — `mod.BitLen()`, the zero-modulus case `LeftPadBytes([]byte{}, modLen)`

`mod.BitLen()`: `DX = len - 1` (`JL` when `len = 0`), smear of the top limb into `R9`, `BSRQ R9, R8` (`fn + 0xa89`),
`DX = (len - 1) << 6 + R8 + 1`; `JNE C2`. Zero modulus: `modLen = 0` returns `(zerobase, 0, 0)`; otherwise
`makeslice(uint8, modLen, modLen)` (return `fn + 0xad1`) and `(buf, modLen, modLen)`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c1 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (Q : Janus.Amd64.Outcome → Prop)
    (W : Nat) (hW : stk ≤ W)
    (B : Nat) (hB : 3 * makeCost 4 + 3 * dCost + allocCost 1024 ≤ B) (hbB : B ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 3 3 (cstD 3) L1 b1 S)
    (hx0 : (S.regs 0).toNat = S.mem.readLE (opAt s 2 + 8) 8) (hx3 : (S.regs 3).toNat = S.mem.readLE (opAt s 2 + 16) 8)
    (hpc : S.rip = BitVec.ofNat 64 pcC1)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b B L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (hk : 0 < opV s p len 2 → ∀ T : State, T.rip = BitVec.ofNat 64 pcC2 → T.mem = S.mem → T.regs 4 = S.regs 4 →
      T.regs 14 = S.regs 14 → T.regs 5 = S.regs 5 → T.xmm 15 = S.xmm 15 → T.fsBase = S.fsBase → T.df = S.df →
      Reaches ((LibRun.program.link impl).withExit ret) T Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, -, -, -, -, -, -, hs3, -, -, -, -, -, hl2, -, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, -⟩ := hrel
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hga hLs hLsS hMF hW
  obtain ⟨hneg, hval, hnorm, h128, hlc, hlive⟩ := hop 2 (by omega)
  simp only [opAt] at hneg hval hnorm h128 hlc hlive hx0 hx3
  simp only [show (s.regs 4).toNat - 136 - 32 * 2 + 8 = (s.regs 4).toNat - 192 by omega,
    show (s.regs 4).toNat - 136 - 32 * 2 + 16 = (s.regs 4).toNat - 184 by omega,
    show (s.regs 4).toNat - 136 - 32 * 2 + 24 = (s.regs 4).toNat - 176 by omega] at hnorm h128 hlc hlive hx0 hx3
  simp only [natAt, show (s.regs 4).toNat - 136 - 32 * 2 + 8 = (s.regs 4).toNat - 192 by omega,
    show (s.regs 4).toNat - 192 + 8 = (s.regs 4).toNat - 184 by omega] at hval
  have hdec : (BitVec.ofNat 64 (hdrV s p len 2)).toNat = hdrV s p len 2 := by simp; omega
  generalize hmpd : S.mem.readLE ((s.regs 4).toNat - 192) 8 = mp at hx0 hval hnorm hlive
  generalize hmld : S.mem.readLE ((s.regs 4).toNat - 184) 8 = ml at hx3 hval hnorm h128 hlc
  by_cases hml : ml = 0
  · -- `mod = 0`
    subst hml
    have hV : opV s p len 2 = 0 := by rw [← hval]; rfl
    have hR : resV s p len = 0 := by simp [resV, hV]
    have hr3 : S.regs 3 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hx3]; rfl)
    clear hval hV hmpd hmld hnorm hlive hlc h128 hneg hop hx0 hx3
    by_cases hz : hdrV s p len 2 = 0
    · have hIz : (BitVec.ofNat 64 (hdrV s p len 2)).toInt = 0 := by rw [hz]; rfl
      have hs3' : S.mem.readLE ((s.regs 4).toNat - 472) 8 = 0 := by rw [hs3, hz]
      janus64_run [hsp, hm1, hm2, hs3', hr3, msb_m1', msb_allones]
      refine hOk _ ⟨by janus64_simp [hsp], by janus64_simp [hm2, regFP], by janus64_simp [h14, regG],
        by janus64_simp [hx15]⟩ ⟨by janus64_simp, by janus64_simp [hz], by rw [hz, hR]; rfl⟩
        ⟨by janus64_simp [hfs], by janus64_simp [hdf], L1, b1, hext, by simp only [cstD] at hbud; omega, ?_,
          by rw [hz]; omega, ?_, ?_⟩
      · dsimp only; exact hinv
      · dsimp only; exact memFrame_win hW hMF
      · dsimp only; exact hLF
    · have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
      have hmk' : MakesliceLiveContract64 (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
        MakesliceLiveContract64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmk
      have hmkP := hmk'.pos L1 b1
      janus_eval_nat h_u : uint8T
      have hokb : R.ok (cA "runtime.makeslice") [7231264, hdrV s p len 2, hdrV s p len 2] := by
        have := hokB _ hl2; rwa [h_u] at this
      have hU2 : S.mem.readLE 7231264 8 = 1 := u8T_size hdS
      have hU3 : S.mem.readLE 7231272 8 = 0 := u8T_ptr hdS
      have hut : Apart 7231264 16 ((s.regs 4).toNat - 4800) (4800 + 40) :=
        apart_of_data (x := 7231264) (l := 16) hd 0 (by decide) (by decide) hw
      unfold Apart at hut
      have hU1 : S.mem.accessible 7231264 16 false = true := by rw [hMF.accessible]; exact u8T_acc hd
      have hBS : blockSize (hdrV s p len 2) true ≤ b1 := (bs_le hl2 hB hbB hbud).1
      have hIp := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
      have hs3' : S.mem.readLE ((s.regs 4).toNat - 472) 8 = (BitVec.ofNat 64 (hdrV s p len 2)).toNat := by rw [hs3, hdec]
      have hpos : (BitVec.ofNat 64 (hdrV s p len 2)).toInt > 0 := by rw [hIp]; simp; omega
      have hLSm : ∀ r ∈ L1, Outside r.fst (r.snd - r.fst)
          ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
              ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
            [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
        intro r hr; have := hLsS r hr
        simp only [LiveSep, win, stk, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
        omega
      obtain ⟨hcf1, hcf2, hcf3, hcf4⟩ := frame_call_facts hal hg3 hga
      set_option janus.callRegions true in
      janus64_run [hsp, hm1, hm2, hs3', hr3, msb_m1', msb_allones, hIp, hpos, hU2, hU3, toInt_small, BitVec.msb_eq_decide]
        until [segAddr Extracted.program fn + 0xad1] calls [hmkP]
      rename_i ptr _ _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k _ hzk hrk hapSk hinvk
      have hMFm : MemFrame S.mem mk (R.rt ++ win s stk 40) := by simp only [win, stk]; janus_frame
      have hMF2 : MemFrame s.mem mk (R.rt ++ win s stk 40) := hMF.trans hMFm fun _ _ h => ⟨h, h⟩
      have hLFS : LiveFrame S.mem mk L1 [] :=
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsS).trans hLFk (fun _ _ h => h)
      have hLF2 : LiveFrame s.mem mk L [] := hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
      have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) :=
        LiveExt.single (by simpa using hink) (by simpa using hapk)
      clear hdS hLsS hLFS hLSm
      janus64_run [hm1, hm2, hs3']
      refine hOk _ ⟨by janus64_simp [hsp], by janus64_simp [hm2, regFP], by janus64_simp [h14, regG],
        by janus64_simp [hx15]⟩ ⟨by janus64_simp, by janus64_simp [hs3, hdec], ?v⟩
        ⟨by janus64_simp [hfs], by janus64_simp [hdf],
          L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)], b1 - blockSize (hdrV s p len 2) true,
          hext.trans hext', ?bud, ?inv, ?held, ?mf, ?lf⟩
      case v =>
        rw [hR]; janus64_simp
        exact beVal_zeros fun i hi => by rw [hzk i (by omega)]; rfl
      case bud => exact (bs_le hl2 hB hbB hbud).2
      case inv => dsimp only; exact hinvk
      case held =>
        intro _
        janus64_simp
        exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega,
          by dsimp only; omega⟩
      case mf => dsimp only; exact memFrame_win hW hMF2
      case lf => dsimp only; exact hLF2
  · have hml1 : 1 ≤ ml := Nat.pos_of_ne_zero hml
    have hq := msb_sub_one_le64 ml hml1 (by omega)
    have hr3 : S.regs 3 = BitVec.ofNat 64 ml := by
      apply BitVec.eq_of_toNat_eq; rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmp : mp < 2 ^ 64 := by rw [← hmpd]; exact Janus.Arm64.Memory.readLE_lt _ _ 8
    have hr0 : S.regs 0 = BitVec.ofNat 64 mp := by
      apply BitVec.eq_of_toNat_eq; rw [hx0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmp]
    obtain ⟨-, -, hpacc, hp48, -, -⟩ := hlive (by omega)
    have hA : S.mem.accessible mp (8 * ml) false = true := by
      rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_read_of_write _
        (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
    have ht : S.mem.readLE (mp + 8 * (ml - 1)) 8 ≠ 0 := hnorm.resolve_left hml
    have ht' : S.mem.readLE (mp + ml * 8 - 8) 8 ≠ 0 := by
      rwa [show mp + ml * 8 - 8 = mp + 8 * (ml - 1) by omega]
    have hV : 0 < opV s p len 2 := by
      rw [← hval]
      obtain ⟨k, rfl⟩ : ∃ k, ml = k + 1 := ⟨ml - 1, by omega⟩
      rw [natVal_succ]
      have : 0 < S.mem.readLE (mp + 8 * k) 8 := Nat.pos_of_ne_zero (by simpa using ht)
      have := Nat.two_pow_pos (64 * k)
      have := Nat.mul_pos this ‹0 < S.mem.readLE (mp + 8 * k) 8›
      omega
    clear hval hnorm hlc hneg hop hx0 hx3 hinv hLsS hdS hLF hext
    janus64_run [hr0, hr3, hq] until [segAddr Extracted.program fn + 0xa4a]
    gen_reg 8 as x with hX
    have hx : x.toNat ≠ 0 := by
      rw [← hX]
      first
        | exact top_ne64 ht'
        | exact top_ne64 ht
        | (simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)]; first | exact ht' | exact ht)
    janus64_run until [segAddr Extracted.program fn + 0xa89]
    gen_reg 9 as y with hY
    have hy : (y.toNat = 0) = False := by
      rw [← hY]; simp only [eq_iff_iff, iff_false]
      repeat (first | apply bv_or_ne_right_shr | apply bv_or_ne_left)
      exact hx
    janus64_run [hr0, hr3, hq, hy] until [segAddr Extracted.program fn + 0xaa4]
    gen_reg 2 as bl with hBl
    have kb : 64 * (ml - 1) < bl.toNat ∧ bl.toNat ≤ 64 * ml := by
      rw [← hBl]; exact blr_val64' _ _ (by simpa using hy) y.isLt hml1 (by omega)
    have hbl : (bl = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro h; rw [h] at kb; simp at kb
    have hbl' : (bl.toNat = 0) = False := by
      simp only [eq_iff_iff, iff_false]; intro h; omega
    janus64_run [hbl, hbl'] until [pcC2]
    exact hk hV _ (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp)

end FvModexp.Amd64.Run
