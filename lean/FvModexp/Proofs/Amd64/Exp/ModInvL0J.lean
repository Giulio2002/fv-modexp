import FvModexp.Proofs.Amd64.Exp.ModInvL0

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `J2` at round `j` from the two `S1` joins (agent infra s58; twin of
`Arm64/Exp/ModInvL0`'s `segL0`)

`segL0`: `runL` / `runF` (`ModInvL0`), the round facts at the callee's entry memory (`mid_L0`), then `callSqr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem toNat_232 {sp : Nat} (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) :
    (BitVec.ofNat 64 (sp - 232)).toNat = sp - 224 - 8 := by
  rw [BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL0 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) {kc kS : Nat} (hsq : SqrE impl R ns kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st xp xl xc n : Nat} {s : State}
    (hsm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a') (hsm' : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (j : Nat)
    (k1L : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204517 (ExL1 s n j) eL kL)
    (k1F : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204903 (ExF n) (eF n) (kF n)) :
    J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s j := by
  intro S p l c q ql qc L1 b1 hpre hn hpc h4 h5 habi h12 h0 h2 h1 h15 h13 h11 h3 h7 h6 h8 h9 h10 hfw hrt hb hz hzz
    hnc hl hlc hqlc hqc hj1 hjn hap' hcong
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  have hmid : Mid R kc L s zp zc st xp xl xc n S.mem L1 b1 p l c q ql qc :=
    ⟨hfw, hrt, hz, hzz, hap', hlc, hqlc, hnc, hqc⟩
  clear hfw hrt hz hzz hap'
  have hsw := hpre.1.2.1
  obtain ⟨-, hsp2, hw⟩ := hsw
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) 232 true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hcst : cost sqrC mulC xl n ≤ b := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnwb : NW n ≤ 2 ^ 12 := by simp only [NW]; omega
  have hpj : 2 ^ j < 2 ^ 64 := by
    have h12 : j - 1 < 12 := (Nat.pow_lt_pow_iff_right (by omega)).1 (by omega : 2 ^ (j - 1) < 2 ^ 12)
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hp : p < 2 ^ 64 := hmid.2.2.1.2.1
  have hc40 : c < 2 ^ 40 := hmid.2.2.1.1
  have hq : q < 2 ^ 64 := hmid.2.2.2.1.2.1
  have hqc40 : qc < 2 ^ 40 := hmid.2.2.2.1.1
  have hl0 : 0 < l := len_pos hcong rfl
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  unfold Goal
  by_cases hr : 2 ^ j < NW n
  · refine runL impl _ _ (s.regs 4).toNat p l c (2 ^ j) (NW n) q ql qc (by omega) (by omega) hr hpj (by omega) S hpc
      h4 hacc h0 h2 h1 h12 h3 h15 h13 h11 ?_
    intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
    have mL' := (mid_L0 hpre hmid (2 ^ j) 6204517 hpj (by decide)).1
    rw [← em] at mL'
    obtain ⟨mL, zL, vL, iL, rL, cL⟩ := mL'
    refine callSqr hap hns hnf hsq hkS hkS1 hsm 0x3a5 (by decide) rfl k1L hpre hn hx0 hdf0 mL hj1 hjn
      (bud_jL hcst hj1 hr) hcong (fun M' h => ⟨slot_keep h (by omega) (by decide) (by decide) iL, hr, rfl⟩) zL vL hl
      (by rw [stkR_congr cL]; exact hb) e4 (e5.trans h5) ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩
      e0 (by rw [e4, toNat_232 (by omega) (by omega)]; exact rL) r0 r3 r1 (r7.trans h7) r6 r8 r9
  · refine runF impl _ _ (s.regs 4).toNat p l c (2 ^ j) (NW n) q ql qc (by omega) (by omega) hr hpj (by omega) S hpc
      h4 hacc h0 h2 h1 h12 h3 h15 h13 h11 ?_
    intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
    have mF' := (mid_L0 hpre hmid (2 ^ j) 6204903 hpj (by decide)).2
    rw [← em] at mF'
    obtain ⟨mF2, zF2, vF2, rF2, cF2⟩ := mF'
    refine callSqr hap hns hnf hsq hkS hkS1 hsm 0x527 (by decide) rfl k1F hpre hn hx0 hdf0 mF2 hj1 hjn
      (bud_jF hcst hjn hsm') hcong (fun _ _ => (by simp only [ExF]; omega)) zF2 vF2 hl
      (by rw [stkR_congr cF2]; exact hb) e4 (e5.trans h5) ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩
      e0 (by rw [e4, toNat_232 (by omega) (by omega)]; exact rF2) r0 r3 r1 (r7.trans h7) r6 r8 r9

end FvModexp.Amd64.ModInv
