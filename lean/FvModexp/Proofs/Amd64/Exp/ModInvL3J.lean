import FvModexp.Proofs.Amd64.Exp.ModInvL3
import FvModexp.Proofs.Amd64.Exp.ModInvL1J

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S3 → S4` compositions (agent infra s58)

`segL3` (loop, `e = 2^j·64` from `RSP - 56`) and `segF4` (final, `e = n`): the run (`ModInvL3`), the round facts at
the callee's entry memory (`mid_st`), then `callT`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem p4_le {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {xl n j k : Nat} :
    P3 sqrC mulC xl n j k + makeCost (2 * NW n + 2) ≤ roundCost sqrC mulC xl n j k := by
  simp only [roundCost, P3, P2, P1]; omega

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL3 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (J : Nat)
    (k4 : S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204667 (ExL3 s n J) eL kL) :
    S3 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204645 (ExL3 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h3 h1 hv hN hql hb
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  obtain ⟨hi, hi64, hr, hJ⟩ := hex
  have hnwb : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  have hrn : S.mem.readLE ((s.regs 4).toNat - 224 + 168) 8 = 2 ^ j * 64 := by
    rw [show (s.regs 4).toNat - 224 + 168 = (s.regs 4).toNat - 56 by omega]; exact hi64
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runL3 impl _ _ (s.regs 4).toNat (2 ^ j * 64) q ql qc (by omega) (by omega) S hpc h4 hacc hrn h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m2, v2, w2, -, n2, c2⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224 - 8) 6204667 (by omega) (by omega)
  rw [← em] at m2 v2 w2 n2 c2
  have zs2 : ZS s S'.mem p l c := by
    rw [em]; exact zs_store _ hzs (by omega) (by omega)
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + 0x43b := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have hm : makeCost (truncNeed ql (2 ^ j * 64)) ≤ makeCost (2 * NW n + 2) :=
    makeCost_mono (tn_le (m := 2 * NW n + 2) (by omega)) (by omega)
  refine callT hap hns hnf htr hkT haT 0x43b (by decide) hpre hx0 hdf0 (e := 2 ^ j * 64) (by omega) m2 (by omega)
    (n2 hN) (bud_okP hb hbud p4_le hm) e4 (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 ?_
  intro s' L' b' ql' hpc' hsp' h5' habi' mid' hsl hzv' f0 f3 f1 hv' hN' hlt hbud' hstk
  have hql' : ql' ≤ NW n := by have := tn_e (ql := ql) (e := 2 ^ j * 64); rw [e64] at this; omega
  have i2 : S'.mem.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ (j + 1) := by rw [em, slot_other (by omega)]; exact hi
  have i3 : S'.mem.readLE ((s.regs 4).toNat - 56) 8 = 2 ^ j * 64 := by rw [em, slot_other (by omega)]; exact hi64
  refine k4 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp', h5', habi', ⟨mid'⟩, hj1, hjn, hbud, hcong⟩ hpc'
    ⟨slot_keep hsl (by omega) (by decide) (by decide) i2, slot_keep hsl (by omega) (by decide) (by decide) i3, hr, hJ⟩
    (zs_keep hsl (by omega) zs2) (by rw [hzv', v2, hzv]) hl0 hl f0 f3 f1
    (by rw [hv', w2, hv]) hN' hql' ?_
  rw [hstk, stkR_congr c2]
  exact bud_stepP hb hbud p4_le hbud' hm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF4 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (k4 : S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6205019 (ExF n) (eF n) (kF n)) :
    S3 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204997 (ExF n) (eF n) (kF n) := by
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
  refine runF4 impl _ _ (s.regs 4).toNat n q ql qc (by omega) (by omega) S hpc h4 hacc hrn h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m2, v2, w2, -, n2, c2⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224 - 8) 6205019 (by omega) (by omega)
  rw [← em] at m2 v2 w2 n2 c2
  have zs2 : ZS s S'.mem p l c := by
    rw [em]; exact zs_store _ hzs (by omega) (by omega)
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + 0x59b := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have hm : makeCost (truncNeed ql n) ≤ makeCost (2 * NW n + 2) :=
    makeCost_mono (tn_le (m := 2 * NW n + 2) (by omega)) (by omega)
  refine callT hap hns hnf htr hkT haT 0x59b (by decide) hpre hx0 hdf0 (e := n) (by omega) m2 (by omega)
    (n2 hN) (bud_okP hb hbud p4_le hm) e4 (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 ?_
  intro s' L' b' ql' hpc' hsp' h5' habi' mid' hsl hzv' f0 f3 f1 hv' hN' hlt hbud' hstk
  have hql' : ql' ≤ NW n := Nat.le_trans hlt tn_e
  refine k4 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp', h5', habi', ⟨mid'⟩, hj1, hjn, hbud, hcong⟩ hpc'
    hex (zs_keep hsl (by omega) zs2) (by rw [hzv', v2, hzv]) hl0 hl f0 f3 f1
    (by rw [hv', w2, hv]) hN' hql' ?_
  rw [hstk, stkR_congr c2]
  exact bud_stepP hb hbud p4_le hbud' hm

end

end FvModexp.Amd64.ModInv
