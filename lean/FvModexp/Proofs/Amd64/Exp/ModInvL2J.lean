import FvModexp.Proofs.Amd64.Exp.ModInvL2

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S2 → S3` compositions (agent infra s58)

`segL2` (loop, `k = min(2^j, len x)`, `2^(j+1)` stored at `RSP - 72`) and `segF3` (final, `k = min(numWords, len x)`):
the run (`ModInvL2`), the round facts at the callee's entry memory (`mid_st`), then `callMul`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL2 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (J : Nat)
    (k3 : S3 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204645 (ExL3 s n J) eL kL) :
    S2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204557 (ExL2 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h3 h1 hv hN hql hqK hb
  have hrc' := hrc
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc'
  obtain ⟨hi, hi64, hr, hJ⟩ := hex
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnwb : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hxc : xc < 2 ^ 40 := hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl : xl ≤ 2 ^ 12 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1; omega
  obtain ⟨-, f32, f40, f48, f56, -, -⟩ := hmid.1
  have sp' : ∀ d, (s.regs 4).toNat - 224 + (224 + d) = (s.regs 4).toNat + d := fun d => by omega
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runL2 impl _ _ (s.regs 4).toNat (2 ^ j) st xp xl xc q ql qc (by omega) (by omega) (by omega) (by omega)
    hxp (by omega) S hpc h4 hacc
    (by rw [show (s.regs 4).toNat - 224 + 152 = (s.regs 4).toNat - 72 by omega]; exact hi)
    (by rw [sp' 40]; exact f40) (by rw [sp' 48]; exact f48) (by rw [sp' 56]; exact f56) (by rw [sp' 32]; exact f32)
    h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m1, v1, w1, -, n1, c1⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224) xp (by omega) (by omega)
  obtain ⟨m2, v2, w2, -, n2, c2⟩ := mid_st hpre m1 (a := (s.regs 4).toNat - 224 + 152) (2 * 2 ^ j) (by omega)
    (by omega)
  obtain ⟨m3, v3, w3, -, n3, c3⟩ := mid_st hpre m2 (a := (s.regs 4).toNat - 224 + 8) (min (2 ^ j) xl) (by omega)
    (by omega)
  obtain ⟨m4, v4, w4, -, n4, c4⟩ := mid_st hpre m3 (a := (s.regs 4).toNat - 224 + 16) xc (by omega) (by omega)
  obtain ⟨m5, v5, w5, -, n5, c5⟩ := mid_st hpre m4 (a := (s.regs 4).toNat - 224 - 8) 6204645 (by omega) (by omega)
  simp only [memL2] at em
  rw [← em] at m5 v5 w5 n5 c5
  have zs5 : ZS s S'.mem p l c := by
    rw [em]
    exact zs_store _ (zs_store _ (zs_store _ (zs_store _ (zs_store _ hzs (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)
  have i5 : S'.mem.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ (j + 1) := by
    rw [em, slot_other (by omega), slot_other (by omega), slot_other (by omega),
      show (s.regs 4).toNat - 72 = (s.regs 4).toNat - 224 + 152 by omega, slot_self (by omega), Nat.pow_succ]; omega
  have i6 : S'.mem.readLE ((s.regs 4).toNat - 56) 8 = 2 ^ j * 64 := by
    rw [em, slot_other (by omega), slot_other (by omega), slot_other (by omega), slot_other (by omega),
      slot_other (by omega)]; exact hi64
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + 0x425 := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have y0 : S'.mem.readLE ((S'.regs 4).toNat + 8) 8 = xp := by
    rw [e4, toNat_232 (by omega) (by omega), sp8 (by omega), em, slot_other (by omega), slot_other (by omega),
      slot_other (by omega), slot_other (by omega), slot_self hxp]
  have y1 : S'.mem.readLE ((S'.regs 4).toNat + 16) 8 = min (kL j) xl := by
    rw [e4, toNat_232 (by omega) (by omega), show (s.regs 4).toNat - 224 - 8 + 16 = (s.regs 4).toNat - 224 + 8 by omega,
      em, slot_other (by omega), slot_other (by omega),
      slot_self (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega))]
  have y2 : S'.mem.readLE ((S'.regs 4).toNat + 24) 8 = xc := by
    rw [e4, toNat_232 (by omega) (by omega), show (s.regs 4).toNat - 224 - 8 + 24 = (s.regs 4).toNat - 224 + 16 by omega,
      em, slot_other (by omega), slot_self (by omega)]
  refine callMul hap hns hnf hmu hkM hkM1 hmm 0x425 (by decide) rfl k3 hpre hn hx0 hdf0 m5 hj1 hjn hbud hcong
    (fun M' h => ⟨slot_keep h (by omega) (by decide) (by decide) i5, slot_keep h (by omega) (by decide) (by decide) i6,
      hr, hJ⟩) zs5 (by rw [v5, v4, v3, v2, v1, hzv]) hl0 hl (by rw [w5, w4, w3, w2, w1, hv]) hql (Nat.le_of_lt hr)
    (Nat.one_le_two_pow) hqK
    (by rw [stkR_congr c5, stkR_congr c4, stkR_congr c3, stkR_congr c2, stkR_congr c1]; exact hb)
    e4 (e5.trans h5) ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 y0 y1 y2
    (S' := S')


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF3 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (k3 : S3 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204997 (ExF n) (eF n) (kF n)) :
    S2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204925 (ExF n) (eF n) (kF n) := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h3 h1 hv hN hql hqK hb
  have hrc' := hrc
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc'
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnwb : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hnw1 : 1 ≤ NW n := by simp only [NW]; omega
  have hxc : xc < 2 ^ 40 := hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl : xl ≤ 2 ^ 12 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1; omega
  obtain ⟨-, f32, f40, f48, f56, -, f104⟩ := hmid.1
  have sp' : ∀ d, (s.regs 4).toNat - 224 + (224 + d) = (s.regs 4).toNat + d := fun d => by omega
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runF3 impl _ _ (s.regs 4).toNat (NW n) st xp xl xc q ql qc (by omega) (by omega) (by omega) (by omega)
    hxp (by omega) S hpc h4 hacc
    (by rw [show (s.regs 4).toNat - 224 + 120 = (s.regs 4).toNat - 104 by omega]; exact f104)
    (by rw [sp' 40]; exact f40) (by rw [sp' 48]; exact f48) (by rw [sp' 56]; exact f56) (by rw [sp' 32]; exact f32)
    h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m1, v1, w1, -, -, c1⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224) xp (by omega) (by omega)
  obtain ⟨m3, v3, w3, -, -, c3⟩ := mid_st hpre m1 (a := (s.regs 4).toNat - 224 + 8) (min (NW n) xl) (by omega)
    (by omega)
  obtain ⟨m4, v4, w4, -, -, c4⟩ := mid_st hpre m3 (a := (s.regs 4).toNat - 224 + 16) xc (by omega) (by omega)
  obtain ⟨m5, v5, w5, -, -, c5⟩ := mid_st hpre m4 (a := (s.regs 4).toNat - 224 - 8) 6204997 (by omega) (by omega)
  simp only [memF3] at em
  rw [← em] at m5 v5 w5 c5
  have zs5 : ZS s S'.mem p l c := by
    rw [em]
    exact zs_store _ (zs_store _ (zs_store _ (zs_store _ hzs (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega)) (by omega) (by omega)
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + 0x585 := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have y0 : S'.mem.readLE ((S'.regs 4).toNat + 8) 8 = xp := by
    rw [e4, toNat_232 (by omega) (by omega), sp8 (by omega), em, slot_other (by omega), slot_other (by omega),
      slot_other (by omega), slot_self hxp]
  have y1 : S'.mem.readLE ((S'.regs 4).toNat + 16) 8 = min (kF n j) xl := by
    rw [e4, toNat_232 (by omega) (by omega), show (s.regs 4).toNat - 224 - 8 + 16 = (s.regs 4).toNat - 224 + 8 by omega,
      em, slot_other (by omega), slot_other (by omega),
      slot_self (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega))]
  have y2 : S'.mem.readLE ((S'.regs 4).toNat + 24) 8 = xc := by
    rw [e4, toNat_232 (by omega) (by omega), show (s.regs 4).toNat - 224 - 8 + 24 = (s.regs 4).toNat - 224 + 16 by omega,
      em, slot_other (by omega), slot_self (by omega)]
  refine callMul hap hns hnf hmu hkM hkM1 hmm 0x585 (by decide) rfl k3 hpre hn hx0 hdf0 m5 hj1 hjn hbud hcong
    (fun _ _ => hex) zs5 (by rw [v5, v4, v3, v1, hzv]) hl0 hl (by rw [w5, w4, w3, w1, hv]) hql (Nat.le_refl _)
    hnw1 hqK
    (by rw [stkR_congr c5, stkR_congr c4, stkR_congr c3, stkR_congr c1]; exact hb)
    e4 (e5.trans h5) ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 y0 y1 y2
    (S' := S')

end

end FvModexp.Amd64.ModInv
