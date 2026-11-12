import FvModexp.Proofs.Arm64.Exp.ModInvPost
import FvModexp.Proofs.Arm64.Exp.ModInvX
import FvModexp.Proofs.Arm64.Exp.LibCallsX

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `zz = zz.sqr(stk, z)` and `z = z.lsh(z, 1)` (agent infra)

Generic in the round kind (see `ModInvPost`): `callSqr` (round start → `S1`), `callLsh` (`S4`'s facts → `S5`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (LshPost fnLsh)

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    {pcv : Nat} {Ex : Nat → Memory → Prop} {E Kx : Nat → Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem postSqr (hkc : 4608 ≤ kc) {stkS aboveS : Nat} (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (k1 : S1 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hb : b - spent sqrC mulC n j ≤ b1)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 pcv) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : SqrPostL R b1 (sqrC l) L1 stkS aboveS q qc st p l S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨q', ql', qc', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hof⟩, ⟨hLE, hbud', hinv'⟩, hsb, hstkA,
    hF', hLF'⟩ := hpost
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv' hsb
  rw [h28] at hinv'
  have hqc' : 0 < qc' := by
    rcases hof with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hmid.2.2.2.2.2.2.2.2
    · omega
  have hq' : q' < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | -
    · exact hmid.2.2.2.1.2.1
    · have := (hlive' hqc').2.2.2; omega
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hkc hmid hS' hkS haS hreg hF' hLF' hLE hinv' hsb.1 hsb.2 hlive' hc40' hq'
    (hof.imp id fun h => h.2) (fun h1 h2 h3 _ => hstkA h1 h2 h3) hlc' hqc'
  have hsp0 : 240 ≤ s.sp.toNat := by have := sp_K hpre; omega
  have hlen : ql' ≤ 2 * NW n + 2 := by
    have := len_le_mul hn' hv' (x := l) (y := l) (natVal_lt _ _ _) (natVal_lt _ _ _)
    omega
  have hmc : sqrC l ≤ sqrC (NW n + 1) := hsm _ _ hl
  exact k1 s' j p l c q' ql' qc' L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc' (hex _ hsl) (zs_keep hsl hsp0 hzs) (hzv2.trans hzv) hl0 hl e0 e1 e2
    (by rw [hv', hzv]) hn' hlen (bud_step0 hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callSqr (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkc : 4608 ≤ kc) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hsc : ∀ x, sqC (stLen s.mem st) x = sqrC x) (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (i : Nat) (hi300 : i < 300) (hpcv : pcv = 1797104 + 4 * i)
    (k1 : S1 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv)
    (hl : l ≤ NW n + 1) (hb : b - spent sqrC mulC n j ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1815584) (h30 : S'.regs 30 = BitVec.ofNat 64 pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h1 : S'.regs 1 = BitVec.ofNat 64 ql) (h2 : S'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : S'.regs 3 = BitVec.ofNat 64 st) (h4 : S'.regs 4 = BitVec.ofNat 64 p) (h5 : S'.regs 5 = BitVec.ofNat 64 l)
    (h6 : S'.regs 6 = BitVec.ofNat 64 c) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqrC mulC b L zp zc st xp xl n s) := by
  subst hpcv
  have hl0 := len_pos hcong hzv
  have hnw : NW n ≤ 2 ^ 12 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hst : st < 2 ^ 64 := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.1; omega
  have hlen : stLen S'.mem st = stLen s.mem st := by rw [hm]; exact stLen_M hmid.2.1
  have hmc : sqrC l ≤ sqrC (NW n + 1) := hsm _ _ hl
  obtain ⟨hcap, hX⟩ := sqrX_at hpre hmid hsp h28 hm hkS haS
  refine LibCalls.sqrCallX hap hns hsq (b := b1) (L := L1) (zp := q) (zl := ql) (zc := qc) (st := st) (x := p)
    (xl := l) (xc := c) (ra_mi hap hnf i hi300) (by rw [hpc, sqr_addr]) h30 h0 h1 h2 h3 h4 h5 h6 hmid.2.2.2.1.2.1
    (by have := hmid.2.2.2.2.2.2.1; have := hmid.2.2.2.1.1; omega) (by have := hmid.2.2.2.1.1; omega) hst
    hmid.2.2.1.2.1 (by omega) (by have := hmid.2.2.1.1; omega) (by omega) ?_ hcap hX
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost _ => ?_
  · rw [hlen, hsc]
    exact sqrPre_at hpre hmid hsp h28 hm hkS haS hl
      (bud_ok0 hb hbud (m := sqrC (NW n + 1)) (by simp only [roundCost]; omega) hmc)
  · rw [hlen, hsc] at hpost
    exact postSqr hkc hkS haS hsm k1 hpre hn hmid hj1 hjn hbud hcong hex hzs hzv hl0 hl hb hsp h28 h18 hm hpc' hsp'
      h28' h18' hreg' hpost

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem postLsh (hkc : 4608 ≤ kc) {stkL aboveL : Nat} (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (k5 : S5 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hqs : QS s M q ql qc) (hzv : natVal M p l = Zv)
    (hl : l ≤ NW n + 1)
    (hv : natVal M q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) % 2 ^ E j) (hnq : NatNorm M q ql)
    (hql : ql ≤ NW n) (hb : b - spent sqrC mulC n j - P4 sqrC mulC n ≤ b1)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 pcv) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : LshPost R b1 L1 stkL aboveL p c p l 1 S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hre, hfr⟩, hgrow, ⟨hLE, hbud', hinv'⟩,
    hF', hLF'⟩ := hpost
  simp only [show (1 : Nat) / 64 = 0 from rfl, Nat.add_zero] at hre hfr hgrow hbud'
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv'
  rw [h28] at hinv'
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  have hnc : NW n + 1 ≤ c := hmid.2.2.2.2.2.2.2.1
  have hc' : NW n + 1 ≤ c' ∧ 0 < c' := by
    by_cases h : l + 1 ≤ c
    · obtain ⟨-, rfl⟩ := hre h; omega
    · have := hgrow (by omega); omega
  have hof : (p' = p ∧ c' = c) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1) := by
    by_cases h : l + 1 ≤ c
    · exact Or.inl (hre h)
    · exact Or.inr (hfr (by omega) hc'.2)
  have hp' : p' < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | -
    · exact hmid.2.2.1.2.1
    · have := (hlive' hc'.2).2.2.2; omega
  obtain ⟨hF2, hLF2, hsb, se0, se2⟩ := nostk hpre hmid.2.1 hS' hkL haL hmid.2.2.1 hF' hLF' hLE
  obtain ⟨mid2, hqv, hsl⟩ := after_z hpre hkc hmid hS' hkL haL hreg hF2 hLF2 hLE hinv' hsb (ain_keep se0 se2) hlive' hc40' hp' hof
    (fun _ _ _ h => absurd ⟨se0, se2⟩ h) hlc' hc'.1
  have hsp0 : 240 ≤ s.sp.toNat := by have := sp_K hpre; omega
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  have hv2 : natVal s'.mem p' l' = Zv * 2 := by rw [hv', hzv, Nat.pow_one]
  have hlen : l' ≤ NW n + 2 := by
    have := len_le_mul hn' hv' (x := l) (y := 1) (natVal_lt _ _ _) (by decide)
    omega
  have hmc : makeCost (l + 1) ≤ makeCost (NW n + 2) := makeCost_mono (by omega) (by omega)
  exact k5 s' j p' l' c' q ql qc L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc' (hex _ hsl) (qs_keep hsl hsp0 hqs) e0 e1 e2 hv2 hn' hlen
    ((hqv ql hqlc).trans hv) (norm_keep hqv hqlc hnq) hql (bud_step hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callLsh (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL)
    (hkc : 4608 ≤ kc) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (i : Nat) (hi300 : i < 300) (hpcv : pcv = 1797104 + 4 * i)
    (k5 : S5 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hqs : QS s M q ql qc) (hzv : natVal M p l = Zv)
    (hl : l ≤ NW n + 1)
    (hv : natVal M q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl) % 2 ^ E j) (hnq : NatNorm M q ql)
    (hql : ql ≤ NW n) (hb : b - spent sqrC mulC n j - P4 sqrC mulC n ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1784560) (h30 : S'.regs 30 = BitVec.ofNat 64 pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 p) (h1 : S'.regs 1 = BitVec.ofNat 64 l) (h2 : S'.regs 2 = BitVec.ofNat 64 c)
    (h3 : S'.regs 3 = BitVec.ofNat 64 p) (h4 : S'.regs 4 = BitVec.ofNat 64 l) (h5 : S'.regs 5 = BitVec.ofNat 64 c)
    (h6 : S'.regs 6 = BitVec.ofNat 64 1) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqrC mulC b L zp zc st xp xl n s) := by
  subst hpcv
  have hl0 := len_pos hcong hzv
  have hnw : NW n ≤ 2 ^ 9 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hc40 : c < 2 ^ 40 := hmid.2.2.1.1
  refine lshCall hap hns hls (b := b1) (L := L1) (zp := p) (zl := l) (zc := c) (x := p) (xl := l) (xc := c) (sh := 1)
    (ra_mi hap hnf i hi300) (by rw [hpc, lsh_addr]) h30 h0 h1 h2 h3 h4 h5 h6 hmid.2.2.1.2.1 (by omega) (by omega)
    hmid.2.2.1.2.1 (by omega) (by decide) (by omega)
    (lshPre_at hpre hmid hsp h28 hm hkL haL (by omega)
      (bud_ok hb hbud (m := makeCost (NW n + 2)) (by simp only [roundCost, P4, P3, P2, P1]; omega)
        (makeCost_mono (by omega) (by omega)))) (by decide) hl0
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost => postLsh hkc hkL haL k5 hpre hn hmid hj1 hjn hbud hcong hex hqs
      hzv hl hv hnq hql hb hsp h28 h18 hm hpc' hsp' h28' h18' hreg' hpost

end

end FvModexp.Arm64.ModInv
