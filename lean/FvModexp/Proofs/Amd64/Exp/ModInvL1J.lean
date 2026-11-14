import FvModexp.Proofs.Amd64.Exp.ModInvL1

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S1 → S2` compositions (agent infra s58)

`segL1` (loop, `e = 2^j·64`) and `segF2` (final, `e = n`): the run (`ModInvL1`), the round facts at the callee's
entry memory (`mid_st`), then `callT`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem tn_le {ql e m : Nat} (h : ql ≤ m) : truncNeed ql e ≤ m := Nat.le_trans (Nat.min_le_left _ _) h

theorem tn_e {ql e : Nat} : truncNeed ql e ≤ (e + 63) / 64 := Nat.min_le_right _ _

theorem e64 (j : Nat) : (2 ^ j * 64 + 63) / 64 = 2 ^ j := by omega

theorem p2_le {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {xl n j k : Nat} :
    P1 sqrC n j + makeCost (2 * NW n + 2) ≤ roundCost sqrC mulC xl n j k := by
  simp only [roundCost, P1]; omega

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL1 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (J : Nat)
    (k2 : S2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204557 (ExL2 s n J) eL kL) :
    S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204517 (ExL1 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h3 h1 hv hN hql hb
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc
  obtain ⟨hi, hr, hJ⟩ := hex
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) 232 true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hnwb : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hpj : 2 ^ j * 64 < 2 ^ 16 := by omega
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runL1 impl _ _ (s.regs 4).toNat (2 ^ j) q ql qc (by omega) (by omega) (by omega) S hpc h4 hacc
    (by rw [show (s.regs 4).toNat - 224 + 152 = (s.regs 4).toNat - 72 by omega]; exact hi) h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m1, v1, w1, -, n1, c1⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224 + 168) (2 ^ j * 64) (by omega)
    (by omega)
  obtain ⟨m2, v2, w2, -, n2, c2⟩ := mid_st hpre m1 (a := (s.regs 4).toNat - 224 - 8) 6204557 (by omega) (by omega)
  rw [← em] at m2 v2 w2 n2 c2
  have zs2 : ZS s S'.mem p l c := by
    rw [em]; exact zs_store _ (zs_store _ hzs (by omega) (by omega)) (by omega) (by omega)
  have i2 : S'.mem.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ j := by
    rw [em, slot_other (by omega), slot_other (by omega)]; exact hi
  have i3 : S'.mem.readLE ((s.regs 4).toNat - 56) 8 = 2 ^ j * 64 := by
    rw [em, slot_other (by omega), show (s.regs 4).toNat - 56 = (s.regs 4).toNat - 224 + 168 by omega,
      slot_self (by omega)]
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + 0x3cd := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have hm : makeCost (truncNeed ql (2 ^ j * 64)) ≤ makeCost (2 * NW n + 2) :=
    makeCost_mono (tn_le hql) (by omega)
  refine callT hap hns hnf htr hkT haT 0x3cd (by decide) hpre hx0 hdf0 (e := 2 ^ j * 64) (by omega) m2 hql
    (n2 (n1 hN)) (bud_okP hb hbud p2_le hm) e4 (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 ?_
  intro s' L' b' ql' hpc' hsp' h5' habi' mid' hsl hzv' f0 f3 f1 hv' hN' hlt hbud' hstk
  have hql' : ql' ≤ 2 ^ j := by have := tn_e (ql := ql) (e := 2 ^ j * 64); rw [e64] at this; omega
  refine k2 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp', h5', habi', ⟨mid'⟩, hj1, hjn, hbud, hcong⟩ hpc'
    ⟨slot_keep hsl (by omega) (by decide) (by decide) i2, slot_keep hsl (by omega) (by decide) (by decide) i3, hr, hJ⟩
    (zs_keep hsl (by omega) zs2) (by rw [hzv', v2, v1, hzv]) hl0 hl f0 f3 f1
    (by rw [hv', w2, w1, hv]) hN' (by omega) hql' ?_
  rw [hstk, stkR_congr c2, stkR_congr c1]
  exact bud_stepP hb hbud p2_le hbud' hm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF2 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (k2 : S2 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204925 (ExF n) (eF n) (kF n)) :
    S1 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204903 (ExF n) (eF n) (kF n) := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h3 h1 hv hN hql hb
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hrn : S.mem.readLE ((s.regs 4).toNat - 224 + 288) 8 = n := by
    rw [show (s.regs 4).toNat - 224 + 288 = (s.regs 4).toNat + 64 by omega]; exact hmid.1.2.2.2.2.2.1
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runF2 impl _ _ (s.regs 4).toNat n q ql qc (by omega) (by omega) S hpc h4 hacc hrn h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m2, v2, w2, -, n2, c2⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224 - 8) 6204925 (by omega) (by omega)
  rw [← em] at m2 v2 w2 n2 c2
  have zs2 : ZS s S'.mem p l c := by
    rw [em]; exact zs_store _ hzs (by omega) (by omega)
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + 0x53d := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have hm : makeCost (truncNeed ql n) ≤ makeCost (2 * NW n + 2) :=
    makeCost_mono (tn_le hql) (by omega)
  refine callT hap hns hnf htr hkT haT 0x53d (by decide) hpre hx0 hdf0 (e := n) (by omega) m2 hql
    (n2 hN) (bud_okP hb hbud p2_le hm) e4 (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 ?_
  intro s' L' b' ql' hpc' hsp' h5' habi' mid' hsl hzv' f0 f3 f1 hv' hN' hlt hbud' hstk
  have hql' : ql' ≤ NW n := Nat.le_trans hlt tn_e
  refine k2 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp', h5', habi', ⟨mid'⟩, hj1, hjn, hbud, hcong⟩ hpc'
    hex (zs_keep hsl (by omega) zs2) (by rw [hzv', v2, hzv]) hl0 hl f0 f3 f1
    (by rw [hv', w2, hv]) hN' hql' hql' ?_
  rw [hstk, stkR_congr c2]
  exact bud_stepP hb hbud p2_le hbud' hm

end

end FvModexp.Amd64.ModInv
