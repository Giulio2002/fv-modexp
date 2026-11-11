import FvModexp.Proofs.Arm64.Exp.ModInvRt

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
    have hok1 : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, NW n + 1, NW n + 5] :=
      hsv.1 _ _ _ (by simp only [NW]; omega)
    have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hty : Outside wT 16 R.rt := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hinv0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmc : makeCost (NW n + 1) = allocCost (8 * (NW n + 5)) := by
      unfold makeCost makeCap; rw [if_neg (show ¬ (NW n + 1 = 1) by simp only [NW]; omega)]
    have hbl := blockSize_le_allocCost (8 * (NW n + 5)) true
    have hbs : blockSize (8 * (NW n + 5)) true ≤ b := by simp only [cost] at hcost; omega
    have hwt : Apart wT 16 (s.sp.toNat - (240 + kc)) (240 + kc + 72) :=
      apart_of_data hd 1 (by decide) (by decide) hw
    obtain ⟨ht8, ht0, hta⟩ := wT_facts hd
    have hwt' : Apart wT 16 (s.sp.toNat - 240 - kc) (kc + 312) := by unfold Apart at hwt ⊢; omega
    have hwTv : wT = 2641088 := rfl
    have hts8 : S.mem.readLE 2641088 8 = 8 := by
      rw [← hwTv, hF.readLE _ _ (by unfold Apart at hwt; simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)]
      exact ht8
    have hts0 : S.mem.readLE (2641088 + 8) 8 = 0 := by
      rw [← hwTv, hF.readLE _ _ (by unfold Apart at hwt; simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)]
      exact ht0
    have hk0 : k0 s xp xl n < 2 ^ 64 := by
      unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
    clear hcost hinv0 hmc hbl hwt hLs hzx hzlive hxh
    janus_run [hr'] until [1797320]
    refine zalloc impl R hmk _ _ b L (s.regs 28).toNat (s.sp.toNat - 240) kc (NW n) _ (S.regs 18) (S.regs 29)
      (env_of hpre ?hF0) hkc (by simp only [NW]; omega) (by simp only [NW]; omega) ?t8 ?t0 ?ta hwt' hty hok1 hbs
      (inv_win (by simp only [K]; omega) hout' ?hF0 hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      st xp xl xc n (n + 63) (NW n) (k0 s xp xl n) ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 _ ?pc ?sp ?h1 ?h9 ?h18 ?h28 ?h29 rfl ?KZ
    case hF0 =>
      refine hF.trans (?_ : MemFrame S.mem _ (winA s (K kc) A)) fun a k h => ⟨h, h⟩
      simp only [winA, K, A]; janus_frame
    case KZ =>
      intro S' m p r e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 hap
      refine kM S' p (NW n + 5) (L ++ [(p, p + r)]) (b - r) hpre hn e1 (by rw [e2]; try (congr 1; omega)) ?_ (e14.trans h18) e3 e4 e5
        e6 e7 e8 e9 e10 e11 e12 e13 (e17 ▸ (alloc_jm hkc hpre ?hF0 ?hrg ?hfw hap).1)
        (e17 ▸ (alloc_jm hkc hpre ?hF0 ?hrg ?hfw hap).2.1) (alloc_jm hkc hpre ?hF0 ?hrg ?hfw hap).2.2.1
        (e17 ▸ (alloc_jm hkc hpre ?hF0 ?hrg ?hfw hap).2.2.2) (by omega)
      · rw [e15, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · refine hF.trans (?_ : MemFrame S.mem _ (winA s (K kc) A)) fun a k h => ⟨h, h⟩
        simp only [winA, K, A]; janus_frame
      · janus_simp; exact hrg
      · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | (janus_simp; done) | (janus_simp; first | exact f1 | exact f2 | exact Nat.mod_eq_of_lt hk0)
    case t8 => have h := hwt'; unfold Apart at h; rw [hwTv] at h ⊢; janus_simp; exact hts8
    case t0 => have h := hwt'; unfold Apart at h; rw [hwTv] at h ⊢; janus_simp; exact hts0
    case ta =>
      have h := hwt'; unfold Apart at h; rw [hwTv] at h ⊢; janus_simp
      rw [hwTv] at hta; exact hta
    case h1 => janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.ModInv
