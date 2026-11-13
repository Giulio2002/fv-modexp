import FvModexp.Proofs.Arm64.Exp.ModInvPostS

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): loop head `J2` → first call of a round (agent infra)

`0x1b6fb0` (nat.go:1326): `z` spilled to `SP - 48 / - 56 / - 16` (len, cap, ptr); `CMP R8->6, R0; BCC` (`i < numWords`):
* loop body `0x1b6eb0`: `i` → `SP - 80`, `zz = zz.sqr(stk, z)` at `0x1b6ecc` (returns to `S1` loop, `0x1b6ed0`);
* exit `0x1b6fc4`: `zz = zz.sqr(stk, z)` at `0x1b6fdc` (returns to `S1` final, `0x1b6fe0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- `z`'s spills at the loop head -/
@[reducible] def memZS (s : State) (M : Memory) (p l c : Nat) : Memory :=
  ((M.writeLE (s.sp.toNat - 240 + 192) 8 l).writeLE (s.sp.toNat - 240 + 184) 8 c).writeLE
    (s.sp.toNat - 240 + 224) 8 p

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `z`'s spills: the round facts survive, `z`'s slots hold it, `z`'s words unchanged -/
theorem store_zs (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hkc : 4608 ≤ kc) :
    Mid R kc L s zp zc st xp xl xc n (memZS s M p l c) L1 b1 p l c q ql qc ∧ ZS s (memZS s M p l c) p l c ∧
      (memZS s M p l c).readLE p (8 * l) = M.readLE p (8 * l) ∧
      (NatNorm M p l → NatNorm (memZS s M p l c) p l) := by
  have hK := sp_K hpre
  have hsp0 : 248 ≤ s.sp.toNat := by omega
  have hp : p < 2 ^ 64 := hmid.2.2.1.2.1
  have hc : c < 2 ^ 40 := hmid.2.2.1.1
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  have F1 := frame_slot (s := s) (kc := kc) M l (a := s.sp.toNat - 240 + 192) (by omega) (by omega)
  have F2 := frame_slot (s := s) (kc := kc) (M.writeLE (s.sp.toNat - 240 + 192) 8 l) c
    (a := s.sp.toNat - 240 + 184) (by omega) (by omega)
  have F3 := frame_slot (s := s) (kc := kc) ((M.writeLE (s.sp.toNat - 240 + 192) 8 l).writeLE
    (s.sp.toNat - 240 + 184) 8 c) p (a := s.sp.toNat - 240 + 224) (by omega) (by omega)
  have w1 := fw2_slot (a := s.sp.toNat - 240 + 192) hmid.1 l hsp0 (by omega) (by omega) (by omega)
  have w2 := fw2_slot (a := s.sp.toNat - 240 + 184) w1 c hsp0 (by omega) (by omega) (by omega)
  have w3 := fw2_slot (a := s.sp.toNat - 240 + 224) w2 p hsp0 (by omega) (by omega) (by omega)
  have m1 := mid_frame hpre hmid F1 (Memory.regions_writeLE _ _ _ _) w1
  have m2 := mid_frame hpre m1 F2 (Memory.regions_writeLE _ _ _ _) w2
  have m3 := mid_frame hpre m2 F3 (Memory.regions_writeLE _ _ _ _) w3
  refine ⟨m3, ⟨?_, ?_, ?_⟩, ?_, fun h => ?_⟩
  · simp only [memZS]
    rw [show s.sp.toNat - 16 = s.sp.toNat - 240 + 224 by omega, Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hp]
  · simp only [memZS]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 48 = s.sp.toNat - 240 + 192 by omega, Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (by omega)]
  · simp only [memZS]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 56 = s.sp.toNat - 240 + 184 by omega, Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (by omega)]
  · exact ((own_read m2.2.2.1 F3 hlc).trans (own_read m1.2.2.1 F2 hlc)).trans (own_read hmid.2.2.1 F1 hlc)
  · exact own_norm m2.2.2.1 F3 hlc (own_norm m1.2.2.1 F2 hlc (own_norm hmid.2.2.1 F1 hlc h))

set_option maxRecDepth 20000 in
/-- the loop body's store of `i` (`SP - 80`) -/
theorem store_i (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hzs : ZS s M p l c) (hkc : 4608 ≤ kc) {i : Nat} (hi : i < 2 ^ 64) :
    Mid R kc L s zp zc st xp xl xc n (M.writeLE (s.sp.toNat - 240 + 160) 8 i) L1 b1 p l c q ql qc ∧
      ZS s (M.writeLE (s.sp.toNat - 240 + 160) 8 i) p l c ∧
      (M.writeLE (s.sp.toNat - 240 + 160) 8 i).readLE (s.sp.toNat - 80) 8 = i ∧
      (M.writeLE (s.sp.toNat - 240 + 160) 8 i).readLE p (8 * l) = M.readLE p (8 * l) ∧
      (NatNorm M p l → NatNorm (M.writeLE (s.sp.toNat - 240 + 160) 8 i) p l) := by
  have hK := sp_K hpre
  have hsp0 : 248 ≤ s.sp.toNat := by omega
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  have F1 := frame_slot (s := s) (kc := kc) M i (a := s.sp.toNat - 240 + 160) (by omega) (by omega)
  have w1 := fw2_slot (a := s.sp.toNat - 240 + 160) hmid.1 i hsp0 (by omega) (by omega) (by omega)
  have m1 := mid_frame hpre hmid F1 (Memory.regions_writeLE _ _ _ _) w1
  refine ⟨m1, zs_store i hzs (by omega) (by omega), ?_, own_read hmid.2.2.1 F1 hlc,
    fun h => own_norm hmid.2.2.1 F1 hlc h⟩
  rw [show s.sp.toNat - 80 = s.sp.toNat - 240 + 160 by omega, Memory.readLE_writeLE_self,
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hi]

/-- a loop round's budget fits (`i = 2^j < numWords`: round `j ≤ log2 numWords`) -/
theorem bud_jL {j : Nat} (hc : cost sqrC mulC xl n ≤ b) (hj1 : 1 ≤ j) (hr : 2 ^ j < NW n) :
    spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (2 ^ j) ≤ b := by
  have hNW0 : NW n ≠ 0 := by have := Nat.two_pow_pos j; omega
  have hjl : j ≤ Nat.log2 (NW n) := (Nat.le_log2 hNW0).2 (Nat.le_of_lt hr)
  have hm := sumR_mono sqrC mulC xl n hjl
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [sumR_succ] at hm
  simp only [spent, cost, Nat.add_sub_cancel] at hc ⊢
  omega

/-- the final round's budget fits (`2^(j-1) < numWords`) -/
theorem bud_jF {j : Nat} (hc : cost sqrC mulC xl n ≤ b) (hjn : 2 ^ (j - 1) < NW n)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a') :
    spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (NW n) ≤ b := by
  have hNW0 : NW n ≠ 0 := by have := Nat.two_pow_pos (j - 1); omega
  have hjl : j - 1 ≤ Nat.log2 (NW n) := (Nat.le_log2 hNW0).2 (Nat.le_of_lt hjn)
  have hm := sumR_mono sqrC mulC xl n hjl
  have hs := hsm _ _ (zB_le hjn)
  simp only [spent, cost, roundCost] at hc ⊢
  omega

end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL0 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {H : Nat} {sqrC : Nat → Nat} (hsq : SqrHypQ impl R ns stkS aboveS sqrC) {kc : Nat}
    (hkc : 4608 ≤ kc) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88) {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (j : Nat) (k1L : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1797840 (ExL1 s n j) eL kL)
    (k1F : S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 1798112 (ExF n) (eF n) (kF n)) :
    J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s j := by
  intro S p l c q ql qc L1 b1 hpre hn hpc hsp h28 h18 h0 h1 h2 h14 h11 h12 h13 h3 h4 h5 h6 h7 h8 h9 hfw hrt hb hz hzz
    hnc hl hlc hqlc hqc hj1 hjn hap' hcong
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpre
  have hsp0 : 240 ≤ s.sp.toNat := by omega
  have hmid : Mid R kc L s zp zc st xp xl xc n S.mem L1 b1 p l c q ql qc :=
    ⟨hfw, hrt, hz, hzz, hap', hlc, hqlc, hnc, hqc⟩
  clear hfw hrt hz hzz hap'
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]; exact hw
  have hcst := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  -- (s45) the budget fact at the memories after the slot stores (never let the elaborator compare `stkR` atoms)
  have ecZ : stCap (memZS s S.mem p l c) st = stCap S.mem st := by
    simp only [memZS]
    rw [cap_slot hpre _ (a := s.sp.toNat - 240 + 224) _ (by omega) (by omega),
      cap_slot hpre _ (a := s.sp.toNat - 240 + 184) _ (by omega) (by omega),
      cap_slot hpre _ (a := s.sp.toNat - 240 + 192) _ (by omega) (by omega)]
  have ec4 : stCap ((memZS s S.mem p l c).writeLE (s.sp.toNat - 240 + 160) 8 (2 ^ j)) st = stCap S.mem st :=
    (cap_slot hpre _ (a := s.sp.toNat - 240 + 160) _ (by omega) (by omega)).trans ecZ
  have hbZ : Box (b - spent sqrC mulC xl n j + stkR H (memZS s S.mem p l c) st ≤ b1) := ⟨by rw [stkR_congr ecZ]; exact hb⟩
  have hb4 : Box (b - spent sqrC mulC xl n j +
      stkR H ((memZS s S.mem p l c).writeLE (s.sp.toNat - 240 + 160) 8 (2 ^ j)) st ≤ b1) :=
    ⟨by rw [stkR_congr ec4]; exact hb⟩
  clear hb ecZ ec4
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  obtain ⟨m3, hzs, hpw, -⟩ := store_zs hpre hmid hkc
  have hn63 : (BitVec.ofNat 64 (n + 63)).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat]; omega
  have h9a := asr_small_bv _ hn63 6 18158513697557839872#64 288230376151711743#64 ⟨by omega, by omega⟩ rfl
  have h9b := asr_small_toNat _ hn63 6 18158513697557839872 288230376151711744 ⟨by omega, by omega⟩ rfl
  have hnw : BitVec.ofNat 64 (n + 63) >>> 6 = BitVec.ofNat 64 (NW n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [NW]; omega
  have hnw' : (BitVec.ofNat 64 (n + 63)).toNat / 2 ^ 6 = NW n := by
    rw [BitVec.toNat_ofNat]; simp only [NW]; omega
  have hnwb : NW n ≤ 2 ^ 12 := by simp only [NW]; omega
  have hss : ((BitVec.ofNat 64 (n + 63)).sshiftRight 6).toNat = NW n := by
    rw [BitVec.toNat_sshiftRight_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.2 (by rw [BitVec.toNat_ofNat]; omega)),
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    simp only [NW]; omega
  have hpj : 2 ^ j < 2 ^ 64 := by
    have h12 : j - 1 < 12 := (Nat.pow_lt_pow_iff_right (by omega)).1 (by omega : 2 ^ (j - 1) < 2 ^ 12)
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hpre' : Box (Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) := ⟨hpre⟩
  have hmid' : Box (Mid R kc L s zp zc st xp xl xc n S.mem L1 b1 p l c q ql qc) := ⟨hmid⟩
  have hm3' := Box.mk m3
  clear hpre hmid m3
  unfold Goal
  by_cases hr : 2 ^ j < NW n
  · obtain ⟨m4, hzs4, hi4, hpw4, -⟩ := store_i hpre'.h hm3'.h hzs hkc hpj
    janus_run [h9a, h9b, hnw, hnw', hss, hr] until [1815584]
    refine callSqr hap hns hnf hsq hkc hkS haS hsm 184 (by decide) rfl k1L hpre'.h hn m4 hj1 hjn
      (bud_jL hcst hj1 hr) hcong
      (fun M' h => ⟨slot_keep h hsp0 (by decide) (by decide) hi4, hr, rfl⟩) hzs4 (hpw4.trans hpw) hl hb4.h _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try janus_simp
  · janus_run [h9a, h9b, hnw, hnw', hss, hr] until [1815584]
    refine callSqr hap hns hnf hsq hkc hkS haS hsm 252 (by decide) rfl k1F hpre'.h hn hm3'.h hj1 hjn
      (bud_jF hcst hjn hsm) hcong
      (fun _ _ => (by simp only [ExF]; omega)) hzs hpw hl hbZ.h _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try janus_simp

end FvModexp.Arm64.ModInv
