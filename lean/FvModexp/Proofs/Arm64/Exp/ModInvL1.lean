import FvModexp.Proofs.Arm64.Exp.ModInvSegC

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): loop round, `S1` → `zz = zz.trunc(zz, i·64)` → `S2` (agent infra)

`+0x2e0` (`0x1b6ed0`): `i·64` (from `SP - 80`) stored to `SP - 64`, `trunc` call at `0x1b6ee8`, returns to `0x1b6eec`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- after `trunc` returns (`0x1b6eec`): `S2` -/
theorem postL1 {J : Nat} {kc : Nat} (hkc : 4608 ≤ kc) {stkT aboveT : Nat} (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {impl : List Segment} {R : RtInv} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (k2 : S2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797868 (ExL2 s n J) eL kL)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hi : M.readLE (s.sp.toNat - 80) 8 = 2 ^ j) (hi64 : M.readLE (s.sp.toNat - 64) 8 = 2 ^ j * 64)
    (hjlt : LJ n J j) (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l) (hl : l ≤ NW n + 1)
    (hv : natVal M q ql = Zv * Zv) (hql : ql ≤ 2 * NW n + 2) (hb : b - spent sqrC mulC n j - P1 sqrC n ≤ b1)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 1797868) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : TruncPost R b1 L1 stkT aboveT q qc q ql (2 ^ j * 64) S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨q', ql', qc', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hreuse, -⟩, -, ⟨hLE, hbud', hinv'⟩,
    hF', hLF'⟩ := hpost
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  obtain ⟨hq1, hq2⟩ := hreuse (by unfold truncNeed; omega)
  subst q' qc'
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv'
  rw [h28] at hinv'
  obtain ⟨hF2, hLF2, hsb, se0, se2⟩ := nostk hpre hmid.2.1 hS' hkT haT hmid.2.2.2.1 hF' hLF' hLE
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hkc hmid hS' hkT haT hreg hF2 hLF2 hLE hinv' hsb (ain_keep se0 se2) hlive' hc40'
    hmid.2.2.2.1.2.1 (Or.inl ⟨rfl, rfl⟩) (fun h => absurd ⟨rfl, rfl⟩ h) hlc' hmid.2.2.2.2.2.2.2.2
  have hsp0 : 240 ≤ s.sp.toNat := by have := sp_K hpre; omega
  have hnw : NW n ≤ 2 ^ 12 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hvl : natVal s'.mem q ql' < 2 ^ (64 * 2 ^ j) := by
    rw [hv', show 64 * 2 ^ j = 2 ^ j * 64 by omega]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hlen : ql' ≤ NW n := Nat.le_trans (len_le hn' hvl) (Nat.le_of_lt hjlt.1)
  have hmc := makeCost_mono (a := truncNeed ql (2 ^ j * 64)) (b := 2 * NW n + 2)
    (by unfold truncNeed; exact Nat.le_trans (Nat.min_le_left _ _) hql) (by omega)
  clear hvl
  exact k2 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc'
    ⟨slot_keep hsl hsp0 (by decide) (by decide) hi, slot_keep hsl hsp0 (by decide) (by decide) hi64, hjlt⟩
    (zs_keep hsl hsp0 hzs) (hzv2.trans hzv) hl0 hl e0 e1 e2 (by rw [hv', hv]) hn' hlen (bud_step hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL1 {J : Nat} {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) {kc : Nat} (hkc : 4608 ≤ kc)
    (hkT : stkT ≤ kc) (haT : aboveT ≤ 88) {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (k2 : S2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797868 (ExL2 s n J) eL kL) :
    S1 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797840 (ExL1 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h1 h2 hv hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  obtain ⟨hi, hjlt⟩ := hex
  have hjlt1 := hjlt.1
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have hq64 : q < 2 ^ 64 := hmidB.h.2.2.2.1.2.1
  have hqc40 : qc < 2 ^ 40 := hmidB.h.2.2.2.1.1
  have hqlc : ql ≤ qc := hmidB.h.2.2.2.2.2.2.1
  have hnw : NW n ≤ 2 ^ 12 := by have := hpreB.h.2.2.2.2.1; simp only [NW]; omega
  have hjb : 2 ^ j < 2 ^ 12 := by omega
  have hi' : S.mem.readLE (s.sp.toNat - 240 + 160) 8 = 2 ^ j := by
    rw [show s.sp.toNat - 240 + 160 = s.sp.toNat - 80 by omega]; exact hi
  have hsh := lsl6_pow j ((Nat.pow_lt_pow_iff_right (by omega)).1 hjb)
  unfold Goal
  janus_run [hi', hsh] until [1786000]
  have hpre := hpreB.h
  have hmid := hmidB.h
  clear hpreB hmidB
  have hsp0 : 248 ≤ s.sp.toNat := by omega
  have ea : s.sp.toNat - 240 + 176 = s.sp.toNat - 64 := by omega
  have hF : MemFrame S.mem (S.mem.writeLE (s.sp.toNat - 240 + 176) 8 (2 ^ j * 64)) (winA s (K kc) A) :=
    frame_slot S.mem _ (by omega) (by omega)
  have hfw := fw2_slot (a := s.sp.toNat - 64) hmid.1 (2 ^ j * 64) hsp0 (by omega) (by omega) (by omega)
  rw [← ea] at hfw
  have hmid' := mid_frame hpre hmid hF (Memory.regions_writeLE _ _ _ _) hfw
  have hqc0 : 0 < qc := hmid.2.2.2.2.2.2.2.2
  refine truncCall2 hap hns htr (zp := q) (zl := ql) (zc := qc) (x := q) (xl := ql) (xc := qc) (n := 2 ^ j * 64)
    (ra_mi hap hnf 191 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq64 (by omega) (by omega) hq64 (by omega) (by omega)
    (by omega) (truncPre_at hpre hmid' rfl ?_ rfl hkT haT (by omega) (by omega) ?_)
    (Or.inl (own_norm hmid.2.2.2.1 hF hqlc hnq)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost => postL1 hkc hkT haT k2 hpre hn hmid' hj1 hjn hbud hcong
      ?_ ?_ hjlt ?_ ?_ hl0 hl ?_ hql hb rfl ?_ ?_ rfl hpc' hsp' h28' h18' hreg' hpost
  all_goals try janus_simp
  · exact bud_ok hb hbud (m := makeCost (2 * NW n + 2)) (by simp only [roundCost, P1]; omega)
      (makeCost_mono (by unfold truncNeed; exact Nat.le_trans (Nat.min_le_left _ _) hql) (by omega))
  · exact hi
  · exact zs_store _ hzs (by omega) (by omega)
  · exact (own_read hmid.2.2.1 hF hmid.2.2.2.2.2.1).trans hzv
  · exact (own_read hmid.2.2.2.1 hF hmid.2.2.2.2.2.2.1).trans hv

end FvModexp.Arm64.ModInv
