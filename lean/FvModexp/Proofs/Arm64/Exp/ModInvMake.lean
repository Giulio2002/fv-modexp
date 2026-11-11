import FvModexp.Proofs.Arm64.Exp.ModInvSeg2

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `J0` → `JM` (nat.go:1308-1316, nat.go:58-69) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4608 ≤ kc)
    (kM : JM impl R kc sqrC mulC b L zp zl zc st xp xl xc n s) :
    J0 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S hpre hn hpc hsp h28 h18 h0 h2 h3 h4 h5 h6 h7 h10 hF hrg hfw r8 r40
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgrt, hLs, hro⟩, hsv, -, hn1, hn2, hzl, hzp, hzc0,
    ⟨hzc40, hzlive, hzw⟩, hx0, hxc, hxc40, hxl12, ⟨-, hxa, hx48, hxh, hxw⟩, -, -, hzx, -⟩ := hpre'
  have hout' := hout
  simp only [K, A] at hw hout hb' ha hga hg3
  rw [show (1797104 + 0x6c : Nat) = 1797212 from rfl] at hpc
  obtain ⟨f1, f2⟩ := hfw
  unfold Goal
  have hn63 : (BitVec.ofNat 64 n + 63#64).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have h8a := asr63_small _ hn63
  have hna : ¬ xp + 8 * (xc - 1) = (zp + 8 * (zc - 1)) % 18446744073709551616 := by
    have ha1 := hzx hzc0; have ha2 := (hzlive hzc0).2.2.2; unfold Apart at ha1; omega
  have h9a := asr_small_bv _ hn63 6 18158513697557839872#64 288230376151711743#64 ⟨by omega, by omega⟩ rfl
  have h9b := asr_small_toNat _ hn63 6 18158513697557839872 288230376151711744 ⟨by omega, by omega⟩ rfl
  have hnw : (BitVec.ofNat 64 n + 63#64) >>> 6 = BitVec.ofNat 64 (NW n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    simp only [NW]; omega
  have hnw' : (BitVec.ofNat 64 n + 63#64).toNat / 2 ^ 6 = NW n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp only [NW]; omega
  janus_run [h8a, hna, h9a, h9b, hnw, hnw'] until [1797300]
  have hnwb : NW n + 1 < 2 ^ 63 := by simp only [NW]; omega
  by_cases hr : NW n + 1 ≤ zc
  · janus_run [hr, hnwb] until [1797452]
    refine kM _ zp zc L b hpre hn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (rt0 hkc hpre ?hF ?hR).1
      (Nat.sub_le _ _) (rt0 hkc hpre ?hF ?hR).2 hr
    case hF =>
      refine hF.trans (?_ : MemFrame S.mem _ (winA s (K kc) A)) fun a k h => ⟨h, h⟩
      simp only [winA, K, A]; janus_frame
    case hR => janus_simp; exact hrg
    all_goals first | (janus_simp; done) | skip
    · janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · have hk0 : k0 s xp xl n < 2 ^ 64 := by
        unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | (janus_simp; done) | (janus_simp; first | exact f1 | exact f2 | exact Nat.mod_eq_of_lt hk0)
  · have hr' : zc < NW n + 1 := by omega
    have hok1 : R.ok (Extracted.program.contractAddr "runtime.makeslice") [NatAdd.wordT, NW n + 1, NW n + 5] :=
      hsv.1 _ _ _ (by simp only [NW]; omega)
    have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hty := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hmc : makeCost (NW n + 1) = allocCost (8 * (NW n + 5)) := by
      unfold makeCost makeCap; rw [if_neg (by simp only [NW]; omega)]
    have hbl := blockSize_le_allocCost (8 * (NW n + 5)) true
    have hbs : blockSize (8 * (NW n + 5)) true ≤ b := by simp only [cost] at hcost; omega
    have hwt : Apart NatAdd.wordT 16 (s.sp.toNat - (240 + kc)) (240 + kc + 72) :=
      apart_of_data hd 1 (by decide) (by decide) hw
    have hinv0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hinvS : R.inv b L (s.regs 28).toNat (view R.rt L S.mem) := inv_win (by simp only [K]; omega) hout' hF hinv0
    have hts : S.mem.readLE NatAdd.wordT 8 = s.mem.readLE NatAdd.wordT 8 := by
      refine hF.readLE _ _ ?_
      unfold Apart at hwt; simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
    have hts2 : S.mem.readLE (NatAdd.wordT + 8) 8 = s.mem.readLE (NatAdd.wordT + 8) 8 := by
      refine hF.readLE _ _ ?_
      unfold Apart at hwt; simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
    have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
      refine hF.readLE _ _ ?_
      unfold Apart at hga; simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
    have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 240 - 4096 ∨ s.sp.toNat - 240 - 8 ≤ r.1) ∧
        (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 240 + 8 ∨ s.sp.toNat - 240 + 8 + 24 ≤ r.1) := by
      intro r hr
      have h1 := hLs r hr
      simp only [win, K, A, outside_cons, outside_nil, and_true] at h1
      clear hpre hF hinvS hinv0 hcost
      omega
    unfold Apart at hwt hga
    janus_data hd
    janus_eval_nat h_t : NatAdd.wordT
    rw [h_t] at hty hok1 hwt hts hts2
    have hts8 : S.mem.readLE 2641088 8 = 8 := by rw [hts]; first | assumption | janus_simp
    have hts0 : S.mem.readLE 2641096 8 = 0 := by rw [hts2]; first | assumption | janus_simp
    janus_run [hr', hnwb, hts8, hts0, hgS] until [1797452] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    trace_state
    sorry

end FvModexp.Arm64.ModInv
