import FvModexp.Proofs.Arm64.Exp.ModInvPost
import FvModexp.Proofs.Arm64.Exp.ModInvX
import FvModexp.Proofs.Arm64.Exp.LibCallsX

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `zz = zz.mul(stk, zz, x[:k])` and the second `zz.trunc` (agent infra)

Generic in the round kind (see `ModInvPost`): `callMul` (`S2`'s facts → `S3`), `callT2` (`S3`'s facts → `S4`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    {pcv : Nat} {Ex : Nat → Memory → Prop} {E Kx : Nat → Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem postMul (hkc : 4608 ≤ kc) {stkM aboveM : Nat} (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (k3 : S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hv : natVal M q ql = Zv * Zv % 2 ^ E j) (hql : ql ≤ NW n) (hKx : Kx j ≤ NW n)
    (hKx1 : 1 ≤ Kx j) (hb : b - spent sqrC mulC n j - P2 sqrC n ≤ b1)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 pcv) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : MulPostL R b1 (mulC ql (min (Kx j) xl)) L1 stkM aboveM q qc st q ql xp (min (Kx j) xl) S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨q', ql', qc', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hof⟩, ⟨hLE, hbud', hinv'⟩, hsb, hstkA,
    hF', hLF'⟩ := hpost
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv' hsb
  rw [h28] at hinv'
  have hxl1 : 0 < xl := hpre.2.2.2.2.2.2.2.2.2.1
  have hk1 : 1 ≤ min (Kx j) xl := by omega
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
  have hxv : natVal M xp (min (Kx j) xl) = natVal s.mem xp (min (Kx j) xl) :=
    x_val hpre hmid.2.1 (Nat.min_le_right _ _)
  have hv2 : natVal s'.mem q' ql' = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) := by
    rw [hv', hv, hxv]
  have hlen : ql' ≤ 2 * NW n := by
    have := len_le_mul hn' hv' (x := ql) (y := min (Kx j) xl) (natVal_lt _ _ _) (natVal_lt _ _ _)
    omega
  have hmc : mulC ql (min (Kx j) xl) ≤ mulC (2 * NW n + 2) (NW n) := hmm _ _ _ _ (by omega) (by omega)
  exact k3 s' j p l c q' ql' qc' L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc' (hex _ hsl) (zs_keep hsl hsp0 hzs) (hzv2.trans hzv) hl0 hl e0 e1 e2 hv2 hn' hlen
    (bud_step hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callMul (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkc : 4608 ≤ kc) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    (hml : ∀ x y, mlC (stLen s.mem st) x y = mulC x y)
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (i : Nat) (hi300 : i < 300) (hpcv : pcv = 1797104 + 4 * i)
    (k3 : S3 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hv : natVal M q ql = Zv * Zv % 2 ^ E j) (hql : ql ≤ NW n) (hKx : Kx j ≤ NW n)
    (hKx1 : 1 ≤ Kx j) (hb : b - spent sqrC mulC n j - P2 sqrC n ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1814128) (h30 : S'.regs 30 = BitVec.ofNat 64 pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h1 : S'.regs 1 = BitVec.ofNat 64 ql) (h2 : S'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : S'.regs 3 = BitVec.ofNat 64 st) (h4 : S'.regs 4 = BitVec.ofNat 64 q) (h5 : S'.regs 5 = BitVec.ofNat 64 ql)
    (h6 : S'.regs 6 = BitVec.ofNat 64 qc) (h7 : S'.regs 7 = BitVec.ofNat 64 xp)
    (h8 : S'.regs 8 = BitVec.ofNat 64 (min (Kx j) xl)) (h9 : S'.regs 9 = BitVec.ofNat 64 xc) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqrC mulC b L zp zc st xp xl n s) := by
  subst hpcv
  have hK := sp_K hpre
  have hnw : NW n ≤ 2 ^ 12 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hst : st < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1; omega
  have hxp : xp < 2 ^ 64 := by have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1; omega
  have hxc : xc < 2 ^ 40 := hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl : xl ≤ 2 ^ 12 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlen : stLen S'.mem st = stLen s.mem st := by rw [hm]; exact stLen_M hmid.2.1
  have hmc : mulC ql (min (Kx j) xl) ≤ mulC (2 * NW n + 2) (NW n) := hmm _ _ _ _ (by omega) (by omega)
  obtain ⟨hcx, hcy, hX⟩ := mulX_at hpre hmid hsp h28 hm hkM haM (Nat.min_le_right (Kx j) xl)
  refine LibCalls.mulCallX hap hns hmu (b := b1) (L := L1) (zp := q) (zl := ql) (zc := qc) (st := st) (x := q)
    (xl := ql) (xc := qc) (y := xp) (yl := min (Kx j) xl) (yc := xc) (ra_mi hap hnf i hi300) (by rw [hpc, mul_addr])
    h30 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hmid.2.2.2.1.2.1 (by have := hmid.2.2.2.1.1; omega)
    (by have := hmid.2.2.2.1.1; omega) hst hmid.2.2.2.1.2.1 (by have := hmid.2.2.2.1.1; omega)
    (by have := hmid.2.2.2.1.1; omega) hxp (by omega) (by omega) (by omega) ?_ hcx hcy hX
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost _ => ?_
  · rw [hlen, hml]
    exact mulPre_at hpre hmid hsp h28 hm hkM haM (Nat.min_le_right _ _) (by omega)
      (bud_ok hb hbud (m := mulC (2 * NW n + 2) (NW n)) (by simp only [roundCost, P2, P1]; omega) hmc)
  · rw [hlen, hml] at hpost
    exact postMul hkc hkM haM hmm k3 hpre hn hmid hj1 hjn hbud hcong hex hzs hzv hl0 hl hv hql hKx hKx1 hb hsp h28 h18 hm
      hpc' hsp' h28' h18' hreg' hpost

end

end FvModexp.Arm64.ModInv
