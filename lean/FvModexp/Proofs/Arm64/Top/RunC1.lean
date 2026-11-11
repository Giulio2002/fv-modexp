import FvModexp.Proofs.Arm64.Top.RunCDefs
import FvModexp.Proofs.Common.GenReg

/-! # `Run` (arm64): `D3` to `C2` or the return — `mod.BitLen()`, the zero-modulus case `LeftPadBytes([]byte{}, modLen)` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (W : Nat) (hW : stk ≤ W) (hWs : W ≤ s.sp.toNat)
    (B : Nat) (hB : 3 * makeCost 4 + 3 * dCost + allocCost 1024 ≤ B) (hbB : B ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 3 L1 b1 S)
    (hx0 : (S.regs 0).toNat = S.mem.readLE (s.sp.toNat - 192) 8) (hx1 : (S.regs 1).toNat = S.mem.readLE (s.sp.toNat - 184) 8)
    (hpc : S.pc = BitVec.ofNat 64 pcC1)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b B L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (hk : 0 < opV s p len 2 → ∀ T : State, T.pc = BitVec.ofNat 64 pcC2 → T.mem = S.mem → T.sp = S.sp →
      T.regs 28 = S.regs 28 → T.regs 29 = S.regs 29 → T.regs 18 = S.regs 18 → T.regs 7 = 64#64 →
      Reaches ((LibRun.program.link impl).withExit ret) T Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  simp only [stk] at hg3 hb' ha hw hout hga hLs hLsS hMF hW
  obtain ⟨hneg, hval, hnorm, h128, hlc, hlive⟩ := hop 2 (by omega)
  simp only [opAt] at hneg hval hnorm h128 hlc hlive
  simp only [show s.sp.toNat - 136 - 32 * 2 + 8 = s.sp.toNat - 192 by omega,
    show s.sp.toNat - 136 - 32 * 2 + 16 = s.sp.toNat - 184 by omega,
    show s.sp.toNat - 136 - 32 * 2 + 24 = s.sp.toNat - 176 by omega] at hnorm h128 hlc hlive
  simp only [natAt, show s.sp.toNat - 136 - 32 * 2 + 8 = s.sp.toNat - 192 by omega,
    show s.sp.toNat - 192 + 8 = s.sp.toNat - 184 by omega] at hval
  have hspn : S.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  generalize hmpd : S.mem.readLE (s.sp.toNat - 192) 8 = mp at hx0 hval hnorm hlive
  generalize hmld : S.mem.readLE (s.sp.toNat - 184) 8 = ml at hx1 hval hnorm h128 hlc
  by_cases hml : ml = 0
  · -- `mod = 0`
    subst hml
    have hV : opV s p len 2 = 0 := by rw [← hval]; rfl
    have hR : resV s p len = 0 := by simp [resV, hV]
    have hr1 : S.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hx1]; rfl)
    clear hval hV hmpd hmld hnorm hlive hlc h128 hneg hop hx0 hx1
    by_cases hz : hdrV s p len 2 = 0
    · have hIz : (BitVec.ofNat 64 (hdrV s p len 2)).toInt = 0 := by rw [hz]; rfl
      janus_run [hm1, hm2, hs3, hr1, hIz]
      refine hOk _ ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29, hm2, regFP],
        by janus_simp [h18, regPlatform]⟩ ⟨by janus_simp, by janus_simp [hz], by rw [hz, hR]; rfl⟩
        ⟨L1, b1, hext, by omega, ?_, by rw [hz]; omega, ?_, ?_⟩
      · dsimp only; exact hinv
      · dsimp only; exact memFrame_win hW hMF
      · dsimp only; exact hLF
    · have hwS : S.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
      have hmk' : MakesliceLiveContract (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
        MakesliceLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmk
      have hmkP := hmk'.pos L1 b1
      janus_eval_nat h_u : uint8T
      have hokb : R.ok (cA "runtime.makeslice") [uint8T, hdrV s p len 2, hdrV s p len 2] := hokB _ hl2
      rw [h_u] at hokb
      have hU2 : S.mem.readLE 2639168 8 = 1 := by
        janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
      have hU3 : S.mem.readLE 2639176 8 = 0 := by
        janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
      have hut : Apart 2639168 16 (s.sp.toNat - 4800) (4800 + 40) :=
        apart_of_data (x := 2639168) (l := 16) hdS 0 (by decide) (by decide) hwS
      unfold Apart at hut
      have hBS : blockSize (hdrV s p len 2) true ≤ b1 := by
        exact (bs_le hl2 hB hbB hbud).1
      have hIp := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
      have hLsL1 : LiveSep L1 (win s 4800 40) := hLsS
      have hU1 : s.mem.accessible 2639168 16 false = true := by
        janus_data hd; exact Memory.accessible_mono _ h_data0 (by omega) (by omega)
      have hLSc : ∀ r ∈ L1, (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 624 - 4096 ∨ s.sp.toNat - 624 - 8 ≤ r.fst) ∧
          (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 624 + 8 ∨ s.sp.toNat - 624 + 8 + 24 ≤ r.fst) := by
        intro r hr; have := hLsL1 r hr
        simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this; omega
      set_option janus.callRegions true in
      janus_run [hm1, hm2, hs3, hr1, hIp, hU2, hU3, toInt_small] until [segAddr Extracted.program fn + 0x7d0] calls [hmkP]
      rename_i ptr _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k h16k hzk hrk hapSk hinvk
      have hMF2 : MemFrame s.mem mk (R.rt ++ winA s stk 40) := by
        simp only [winA, stk] at hMF ⊢
        refine (hMF.trans ?w1 fun a n h => ⟨h, out_wA h⟩).trans hMFk fun a n h => ⟨h, out_cs hb' h⟩
        case w1 => janus_frame
      have hLFS : LiveFrame S.mem mk L1 [] :=
        (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans hLFk (fun _ _ h => h)
      have hLF2 : LiveFrame s.mem mk L [] := hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
      have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) :=
        LiveExt.single (by simpa using hink) (by simpa using hapk)
      clear hdS hLsS hLsL1 hLFS
      janus_run [hm1, hm2]
      refine hOk _ ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29, hm2, regFP],
        by janus_simp [h18, regPlatform]⟩ ⟨by janus_simp, by janus_simp [hs3], ?v⟩
        ⟨L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)], b1 - blockSize (hdrV s p len 2) true,
          hext.trans hext', ?bud, ?inv, ?held, ?mf, ?lf⟩
      case v =>
        rw [hR]; janus_simp
        exact beVal_zeros fun i hi => by rw [hzk i (by omega)]; rfl
      case bud => exact (bs_le hl2 hB hbB hbud).2
      case inv => dsimp only; exact hinvk
      case held =>
        intro _
        have hsz := hrk
        janus_simp
        exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega,
          by dsimp only; omega⟩
      case mf => dsimp only; exact memFrame_win hW hMF2
      case lf => dsimp only; exact hLF2
  · have hml1 : 1 ≤ ml := Nat.pos_of_ne_zero hml
    have hq := msb_sub_one_le ml hml1 (by omega)
    have hr1 : S.regs 1 = BitVec.ofNat 64 ml := by
      apply BitVec.eq_of_toNat_eq; rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmp : mp < 2 ^ 64 := by rw [← hmpd]; exact Memory.readLE_lt _ _ 8
    have hr0 : S.regs 0 = BitVec.ofNat 64 mp := by
      apply BitVec.eq_of_toNat_eq; rw [hx0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmp]
    obtain ⟨-, -, hpacc, hp48⟩ := hlive (by omega)
    have hA : S.mem.accessible mp (8 * ml) false = true := by
      rw [hMF.accessible]; exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
    have ht : S.mem.readLE (mp + 8 * (ml - 1)) 8 ≠ 0 := hnorm.resolve_left hml
    have hV : 0 < opV s p len 2 := by
      rw [← hval]
      obtain ⟨k, rfl⟩ : ∃ k, ml = k + 1 := ⟨ml - 1, by omega⟩
      rw [natVal_succ]
      have : 0 < S.mem.readLE (mp + 8 * k) 8 := Nat.pos_of_ne_zero (by simpa using ht)
      have := Nat.two_pow_pos (64 * k)
      have := Nat.mul_pos this ‹0 < S.mem.readLE (mp + 8 * k) 8›
      omega
    clear hval hnorm hlc hneg hop hx0 hx1 hinv hLsS hdS hLF hext
    janus_run [hr0, hr1, hq] until [segAddr Extracted.program fn + 0x784]
    generalize hxd : BitVec.ofNat 64 (S.mem.readLE (mp + 8 * (ml - 1)) 8) = x
    janus_run until [segAddr Extracted.program fn + 0x7a0]
    gen_reg 5 as bl with hBl
    have kb : 64 * (ml - 1) < bl.toNat ∧ bl.toNat ≤ 64 * ml := by
      rw [← hBl]; refine blr_val' _ _ ?_ ?_ hml1 (by omega)
      · repeat apply or_pos_left'
        rw [← hxd]; exact toNat_ofNat_readLE_pos _ _ ht
      · repeat (first | apply Nat.or_lt_two_pow | exact BitVec.isLt _)
    have hbl : (bl = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro h; rw [h] at kb; simp at kb
    janus_run [hbl] until [pcC2]
    exact hk hV _ (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      (by janus_simp)

end FvModexp.Arm64.Run
