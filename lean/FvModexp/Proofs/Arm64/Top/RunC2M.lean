import FvModexp.Proofs.Arm64.Top.RunC2Sum
import FvModexp.Proofs.Arm64.Top.RunC2Lem2

/-! # `Run` (arm64): `C2` to `V` when `base = 1` (`base.BitLen() == 1`): `v = base.Mod(base, mod).Bytes()` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem clz_one : clzNat 64 1 = 63 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2m (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hM : RunIface.ModSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (Q : Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 28).toNat + 16) 8 L)
    (hbB : okB s p len ≤ b)
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 L1 b1 T)
    (hpc : T.pc = BitVec.ofNat 64 pcC2) (h7 : T.regs 7 = 64#64)
    (hv0 : opV s p len 0 = 1) (hv2 : 0 < opV s p len 2)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.pc = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have henvW0 := henvW
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henvW
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  simp only [stk] at hLsS hMF
  have hspn : T.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  -- the base operand is the one-limb nat `1`
  obtain ⟨hneg0, hval0, hnorm0, h1280, hlc0, hlive0⟩ := hop 0 (by omega)
  simp only [opAt, natAt, show s.sp.toNat - 136 - 32 * 0 + 8 = s.sp.toNat - 128 by omega,
    show s.sp.toNat - 128 + 8 = s.sp.toNat - 120 by omega,
    show s.sp.toNat - 136 - 32 * 0 + 16 = s.sp.toNat - 120 by omega,
    show s.sp.toNat - 136 - 32 * 0 + 24 = s.sp.toNat - 112 by omega] at hneg0 hval0 hnorm0 h1280 hlc0 hlive0
  rw [hv0] at hval0
  obtain ⟨hn1, hx1⟩ := natVal_eq_one hnorm0 hval0
  obtain ⟨-, -, hb0acc, hb048, -, -⟩ := hlive0 (by omega)
  have hA : T.mem.accessible (T.mem.readLE (s.sp.toNat - 128) 8) 8 false = true := by
    rw [hMF.accessible]; exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hb0acc (Nat.le_refl _) (by omega))
  have hb0' : BitVec.ofNat 64 (T.mem.readLE (s.sp.toNat - 128) 8) + 0#64 <<< 3 =
      BitVec.ofNat 64 (T.mem.readLE (s.sp.toNat - 128) 8) := by simp
  -- the Mod call: IntPre outside the run
  have hxs : ∀ a ∈ [s.sp.toNat - 136, s.sp.toNat - 200], ∃ j, j < 3 ∧ a = opAt s j := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, by omega, by simp only [opAt]; omega⟩
    · exact ⟨2, by omega, by simp only [opAt]; omega⟩
  have hpw : [s.sp.toNat - 136, s.sp.toNat - 200].Pairwise
      fun a a' => ∃ i j, i < j ∧ j < 3 ∧ a = opAt s i ∧ a' = opAt s j := by
    refine List.Pairwise.cons (fun a' ha' => ?_) (List.pairwise_singleton _ _)
    simp only [List.mem_singleton] at ha'; subst ha'
    exact ⟨0, 2, by omega, by omega, by simp only [opAt]; omega, by simp only [opAt]; omega⟩
  have hBm : RunIface.ModBudget (max (RunIface.lenW T.mem (s.sp.toNat - 136)) (RunIface.lenW T.mem (s.sp.toNat - 200)))
      ≤ b1 := by
    sorry
  have hIP : ∀ t : State, t.sp = T.sp → t.mem = T.mem → t.regs 28 = s.regs 28 →
      RunIface.IntPre R b1 (RunIface.ModBudget (max (RunIface.lenW T.mem (s.sp.toNat - 136))
        (RunIface.lenW T.mem (s.sp.toNat - 200)))) L1 stkM aboveM [s.sp.toNat - 136, s.sp.toNat - 200] t :=
    fun t h1 h2 h3 => intPre_ops _ (by rw [h1]; exact hspn) h2 h3 henvW0 hW hW1 hab hglob hgL hsv hBm hdS hext hinv hMF
      hop hopA hxs hpw
  have hMod := modW impl hap R stkM aboveM hM b1 L1 T.sp (s.regs 28) T.mem (s.sp.toNat - 136) (s.sp.toNat - 200) hIP
    sorry sorry sorry
  janus_run [hn1, hx1, h7, clz_one, hb0'] until [segAddr Extracted.program fn + 0x85c, segAddr Extracted.program fn + 0x864] calls [hP := hMod]
  obtain ⟨⟨⟨hsp1, h281, h291, h181⟩, hr01, hpost, hyv⟩, hrg1⟩ := hP
  dsimp only at hsp1 h281 h291 h181 hrg1
  have h281' : s'.regs 28 = s.regs 28 := by rw [h281]; janus_simp [h28]
  have hgz : Apart RunIface.gA 32 (s.sp.toNat - 136) 32 := by
    have := hglob.2.2.2.2.2.2.2.2.2
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this; unfold Apart; omega
  have hga : 0 < T.mem.readLE (s.sp.toNat - 136 + 24) 8 →
      Apart RunIface.gA 32 (T.mem.readLE (s.sp.toNat - 136 + 8) 8) (8 * T.mem.readLE (s.sp.toNat - 136 + 24) 8) := by
    rw [show s.sp.toNat - 136 + 24 = s.sp.toNat - 112 by omega, show s.sp.toNat - 136 + 8 = s.sp.toNat - 128 by omega]
    intro hc
    exact InRanges.apart (hlive0 hc).2.2.2.2.1 hglob.2.2.2.2.2.2.2.2.1
  have hlb : RunIface.lenW s'.mem (s.sp.toNat - 136) ≤ RunIface.maxW := by
    sorry
  have hBB : RunIface.ModBudget (max (RunIface.lenW T.mem (s.sp.toNat - 136)) (RunIface.lenW T.mem (s.sp.toNat - 200))) +
      RunIface.BytesBudget (RunIface.lenW s'.mem (s.sp.toNat - 136)) ≤ b1 := by
    have l0 : RunIface.lenW T.mem (s.sp.toNat - 136) ≤ opW s p len 0 := lenW_op (hop 0 (by omega)) (by omega)
    have l2 : RunIface.lenW T.mem (s.sp.toNat - 200) ≤ opW s p len 2 := lenW_op (hop 2 (by omega)) (by omega)
    simp only [okB, callB] at hbB
    exact budget_mod (w := wMax s p len) (Nat.le_trans l0 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)))
      (Nat.le_trans l2 (Nat.le_max_right _ _)) hlb hbud hbB
  obtain ⟨L2, b2, hext2, hb2, hv1, hinv2, hok2, hMF2, hLF2, hIPb⟩ :=
    afterInt hIP hpost hsp.symm rfl (by janus_simp [h28]) hrg1 hgz hga hBB
  have hBy' := bytesW impl hap R stkM aboveM hBy b2 L2 (s.sp - 624#64) (s.regs 28) s'.mem (s.sp.toNat - 136)
    (fun t h1 h2 h3 => hIPb t h1 h2 (h3.trans (by janus_simp [h28]))) hlb
  have hz136 : (s.sp - 136#64).toNat = s.sp.toNat - 136 := by rw [BitVec.toNat_sub]; simp; omega
  janus_run [hsp1, h281', hr01, hz136] until [pcCV] calls [hQ := hBy']
  all_goals (trace_state; sorry)

end FvModexp.Arm64.Run
