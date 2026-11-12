import FvModexp.Proofs.Arm64.Exp.ModInvSegC
import FvModexp.Proofs.Arm64.Exp.ModInvX
import FvModexp.Proofs.Arm64.Exp.LibCallsX

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): loop round, `S2` → `zz = zz.mul(stk, zz, x[:min(i, len x)])` → `S3`
(agent infra)

`0x1b6eec`: `2i` stored to `SP - 80`, `k = min(i, len x)` (`CMP`/`CSEL LO`), `mul` call at `0x1b6f1c`, returns to
`0x1b6f20`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- after `mul` returns (`0x1b6f20`): `S3` -/
theorem postL2 {J : Nat} {kc : Nat} (hkc : 4608 ≤ kc) {stkM aboveM : Nat} (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    {impl : List Segment} {R : RtInv} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (k3 : S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797920 (ExL3 s n J) eL kL)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hi : M.readLE (s.sp.toNat - 80) 8 = 2 ^ (j + 1)) (hi64 : M.readLE (s.sp.toNat - 64) 8 = 2 ^ j * 64)
    (hjlt : LJ n J j) (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l) (hl : l ≤ NW n + 1)
    (hv : natVal M q ql = Zv * Zv % 2 ^ (2 ^ j * 64)) (hql : ql ≤ NW n)
    (hb : b - spent sqrC mulC n j - P2 sqrC n ≤ b1)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 1797920) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : MulPostL R b1 (mulC ql (min (2 ^ j) xl)) L1 stkM aboveM q qc st q ql xp (min (2 ^ j) xl) S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨q', ql', qc', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hof⟩, ⟨hLE, hbud', hinv'⟩, hsb, hstkA,
    hF', hLF'⟩ := hpost
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv' hsb
  rw [h28] at hinv'
  have hxl1 : 0 < xl := hpre.2.2.2.2.2.2.2.2.2.1
  have hk1 : 1 ≤ min (2 ^ j) xl := by have := Nat.one_le_two_pow (n := j); omega
  have hqc' : 0 < qc' := by
    rcases hof with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hmid.2.2.2.2.2.2.2.2
    · omega
  have hq' : q' < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | -
    · exact hmid.2.2.2.1.2.1
    · have := (hlive' hqc').2.2.2; omega
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hkc hmid hS' hkM haM hreg hF' hLF' hLE hinv' hsb.1 hsb.2 hlive' hc40' hq'
    (hof.imp id fun h => h.2) (fun h1 h2 h3 _ => hstkA h1 h2 h3) hlc' hqc'
  have hsp0 : 240 ≤ s.sp.toNat := by have := sp_K hpre; omega
  have hxv : natVal M xp (min (2 ^ j) xl) = natVal s.mem xp (min (2 ^ j) xl) :=
    x_val hpre hmid.2.1 (Nat.min_le_right _ _)
  have hv2 : natVal s'.mem q' ql' = Zv * Zv % 2 ^ eL j * natVal s.mem xp (min (kL j) xl) := by
    rw [hv', hv, hxv]
  have hlen : ql' ≤ 2 * NW n := by
    have := len_le_mul hn' hv' (x := ql) (y := min (2 ^ j) xl) (natVal_lt _ _ _) (natVal_lt _ _ _)
    omega
  have hmc : mulC ql (min (2 ^ j) xl) ≤ mulC (2 * NW n + 2) (NW n) := hmm _ _ _ _ (by omega) (by omega)
  exact k3 s' j p l c q' ql' qc' L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc'
    ⟨slot_keep hsl hsp0 (by decide) (by decide) hi, slot_keep hsl hsp0 (by decide) (by decide) hi64, hjlt⟩
    (zs_keep hsl hsp0 hzs) (hzv2.trans hzv) hl0 hl e0 e1 e2 hv2 hn' hlen (bud_step hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- at `mul`'s entry (`0x1bae70`): the call -/
theorem callL2 {J : Nat} {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) {kc : Nat}
    (hkc : 4608 ≤ kc) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88) {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hml : ∀ x y, mlC (stLen s.mem st) x y = mulC x y)
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (k3 : S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797920 (ExL3 s n J) eL kL)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hi : M.readLE (s.sp.toNat - 80) 8 = 2 ^ j) (hi64 : M.readLE (s.sp.toNat - 64) 8 = 2 ^ j * 64)
    (hjlt : LJ n J j) (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l) (hl : l ≤ NW n + 1)
    (hv : natVal M q ql = Zv * Zv % 2 ^ (2 ^ j * 64)) (hql : ql ≤ NW n)
    (hb : b - spent sqrC mulC n j - P2 sqrC n ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M.writeLE (s.sp.toNat - 240 + 160) 8 (2 ^ (j + 1)))
    (hpc : S'.pc = BitVec.ofNat 64 1814128) (h30 : S'.regs 30 = BitVec.ofNat 64 1797920)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h1 : S'.regs 1 = BitVec.ofNat 64 ql) (h2 : S'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : S'.regs 3 = BitVec.ofNat 64 st) (h4 : S'.regs 4 = BitVec.ofNat 64 q) (h5 : S'.regs 5 = BitVec.ofNat 64 ql)
    (h6 : S'.regs 6 = BitVec.ofNat 64 qc) (h7 : S'.regs 7 = BitVec.ofNat 64 xp)
    (h8 : S'.regs 8 = BitVec.ofNat 64 (min (2 ^ j) xl)) (h9 : S'.regs 9 = BitVec.ofNat 64 xc) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R kc sqrC mulC b L zp zc st xp xl n s s') := by
  have hK := sp_K hpre
  have hsp0 : 248 ≤ s.sp.toNat := by omega
  have hF : MemFrame M (M.writeLE (s.sp.toNat - 240 + 160) 8 (2 ^ (j + 1))) (winA s (K kc) A) :=
    frame_slot M _ (by omega) (by omega)
  have hfw := fw2_slot (a := s.sp.toNat - 80) hmid.1 (2 ^ (j + 1)) hsp0 (by omega) (by omega) (by omega)
  rw [show s.sp.toNat - 80 = s.sp.toNat - 240 + 160 by omega] at hfw
  have hmid' := mid_frame hpre hmid hF (Memory.regions_writeLE _ _ _ _) hfw
  have hnw : NW n ≤ 2 ^ 12 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hst : st < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1; omega
  have hxp : xp < 2 ^ 64 := by have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1; omega
  have hxc : xc < 2 ^ 40 := hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl : xl ≤ 2 ^ 12 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlen : stLen S'.mem st = stLen s.mem st := by rw [hm]; exact stLen_M hmid'.2.1
  have hmc : mulC ql (min (2 ^ j) xl) ≤ mulC (2 * NW n + 2) (NW n) := hmm _ _ _ _ (by omega) (by omega)
  obtain ⟨hcx, hcy, hX⟩ := mulX_at hpre hmid' hsp h28 hm hkM haM (Nat.min_le_right (2 ^ j) xl)
  refine LibCalls.mulCallX hap hns hmu (b := b1) (L := L1) (zp := q) (zl := ql) (zc := qc) (st := st) (x := q)
    (xl := ql) (xc := qc) (y := xp) (yl := min (2 ^ j) xl) (yc := xc) (ra_mi hap hnf 204 (by omega))
    (by rw [hpc, mul_addr]) h30 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hmid.2.2.2.1.2.1 (by have := hmid.2.2.2.1.1; omega)
    (by have := hmid.2.2.2.1.1; omega) hst hmid.2.2.2.1.2.1 (by have := hmid.2.2.2.1.1; omega)
    (by have := hmid.2.2.2.1.1; omega) hxp (by omega) (by omega) (by omega) ?_ hcx hcy hX
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost _ => ?_
  · rw [hlen, hml]
    exact mulPre_at hpre hmid' hsp h28 hm hkM haM (Nat.min_le_right _ _) (by omega)
      (bud_ok hb hbud (m := mulC (2 * NW n + 2) (NW n)) (by simp only [roundCost, P2, P1]; omega) hmc)
  · rw [hlen, hml] at hpost
    exact postL2 hkc hkM haM hmm k3 hpre hn hmid' hj1 hjn hbud hcong
      (by rw [show s.sp.toNat - 80 = s.sp.toNat - 240 + 160 by omega, Memory.readLE_writeLE_self,
          show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]
          exact Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega))
      ((Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans hi64) hjlt (zs_store _ hzs (by omega) (by omega))
      ((own_read hmid.2.2.1 hF hmid.2.2.2.2.2.1).trans hzv) hl0 hl
      ((own_read hmid.2.2.2.1 hF hmid.2.2.2.2.2.2.1).trans hv) hql hb hsp h28 h18 hm hpc' hsp' h28' h18' hreg' hpost

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL2 {J : Nat} {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) {kc : Nat}
    (hkc : 4608 ≤ kc) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88) {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hml : ∀ x y, mlC (stLen s.mem st) x y = mulC x y)
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (k3 : S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797920 (ExL3 s n J) eL kL) :
    S2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s 1797868 (ExL2 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h1 h2 hv hnq hql hb
  obtain ⟨hpreB, hn, hsp, h28, h18, hmidB, hj1, hjn, hbud, hcong⟩ := hrc
  obtain ⟨hi, hi64, hjlt⟩ := hex
  have hjlt1 := hjlt.1
  have hK : 240 + kc ≤ s.sp.toNat := sp_K hpreB.h
  obtain ⟨hal, hb', ha, hw⟩ := hpreB.h.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hmidB.h.2.1.2.1.accessible]; exact hw
  have hfw := hmidB.h.1
  have hjb : 2 ^ j < 2 ^ 12 := by
    have := hpreB.h.2.2.2.2.1; have : NW n ≤ 2 ^ 12 := by simp only [NW]; omega
    omega
  have hi' : S.mem.readLE (s.sp.toNat - 240 + 160) 8 = 2 ^ j := by
    rw [show s.sp.toNat - 240 + 160 = s.sp.toNat - 80 by omega]; exact hi
  have r288 : S.mem.readLE (s.sp.toNat - 240 + 288) 8 = xl := by
    rw [show s.sp.toNat - 240 + 288 = s.sp.toNat + 48 by omega]; exact hfw.2.2.2.1
  have r272 : S.mem.readLE (s.sp.toNat - 240 + 272) 8 = st := by
    rw [show s.sp.toNat - 240 + 272 = s.sp.toNat + 32 by omega]; exact hfw.2.1
  have r280 : S.mem.readLE (s.sp.toNat - 240 + 280) 8 = xp := by
    rw [show s.sp.toNat - 240 + 280 = s.sp.toNat + 40 by omega]; exact hfw.2.2.1
  have r296 : S.mem.readLE (s.sp.toNat - 240 + 296) 8 = xc := by
    rw [show s.sp.toNat - 240 + 296 = s.sp.toNat + 56 by omega]; exact hfw.2.2.2.2.1
  have hadd : BitVec.ofNat 64 (2 ^ j) + BitVec.ofNat 64 (2 ^ j) = BitVec.ofNat 64 (2 ^ (j + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.pow_succ]; omega
  have hxl : xl ≤ 2 ^ 12 := hpreB.h.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hfw
  unfold Goal
  by_cases hc : xl < 2 ^ j
  · have hk : min (2 ^ j) xl = xl := Nat.min_eq_right (by omega)
    janus_run [hi', r288, r272, r280, r296, hadd, hc] until [1814128]
    refine callL2 hap hns hnf hmu hkc hkM haM hml hmm k3 hpreB.h hn hmidB.h hj1 hjn hbud hcong hi hi64 hjlt hzs hzv
      hl0 hl hv hql hb _ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hk]; janus_simp) ?_
    all_goals janus_simp
  · have hk : min (2 ^ j) xl = 2 ^ j := Nat.min_eq_left (by omega)
    janus_run [hi', r288, r272, r280, r296, hadd, hc] until [1814128]
    refine callL2 hap hns hnf hmu hkc hkM haM hml hmm k3 hpreB.h hn hmidB.h hj1 hjn hbud hcong hi hi64 hjlt hzs hzv
      hl0 hl hv hql hb _ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hk]; janus_simp) ?_
    all_goals janus_simp

end FvModexp.Arm64.ModInv
