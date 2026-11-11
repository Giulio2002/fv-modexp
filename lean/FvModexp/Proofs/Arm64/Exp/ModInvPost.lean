import FvModexp.Proofs.Arm64.Exp.ModInvSegC

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the round's calls, generic in the round kind (agent infra)

At a callee entry `S'` (registers set, round facts `Mid` at `S'.mem`): the call and the facts at its return (the next
join). One lemma per callee kind (`zz.sqr`, first `zz.trunc`, `zz.mul`, second `zz.trunc`, `z.lsh`), for the loop
round and the final round alike (`pcv` the return address = the next join, `Ex` its slot facts, `E` the `trunc` width,
`Kx` the `x` prefix length). The segment modules run the few instructions from a join to the callee entry and apply
these.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (LshPost fnLsh)

/-- the goal of every segment -/
@[reducible] def GoalQ (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s : State) : State → Prop := fun s' =>
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    Post R kc sqrC mulC b L zp zc st xp xl n s s'

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    {pcv : Nat} {Ex : Nat → Memory → Prop} {E Kx : Nat → Nat}

/-! ## first `zz.trunc(zz, e)`: `S1`'s facts → `S2` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem postT1 (hkc : 4608 ≤ kc) {stkT aboveT : Nat} (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (k2 : S2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hv : natVal M q ql = Zv * Zv) (hql : ql ≤ 2 * NW n + 2)
    (hb : b - spent sqrC mulC n j - P1 sqrC n ≤ b1) (hE : E j ≤ 64 * NW n)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 pcv) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : TruncPost R b1 L1 stkT aboveT q qc q ql (E j) S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨q', ql', qc', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hreuse, -⟩, -, ⟨hLE, hbud', hinv'⟩,
    hF', hLF'⟩ := hpost
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  obtain ⟨hq1, hq2⟩ := hreuse (by unfold truncNeed; omega)
  subst q' qc'
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv'
  rw [h28] at hinv'
  obtain ⟨hF2, hLF2, hsb, -, -⟩ := nostk hpre hmid.2.1 hS' hkT haT hmid.2.2.2.1 hF' hLF' hLE
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hkc hmid hS' hkT haT hreg hF2 hLF2 hLE hinv' hsb hlive' hc40'
    hmid.2.2.2.1.2.1 (Or.inl ⟨rfl, rfl⟩) (fun h => absurd ⟨rfl, rfl⟩ h) hlc' hmid.2.2.2.2.2.2.2.2
  have hsp0 : 240 ≤ s.sp.toNat := by have := sp_K hpre; omega
  have hvl : natVal s'.mem q ql' < 2 ^ (64 * NW n) := by
    rw [hv']; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) hE)
  have hlen : ql' ≤ NW n := len_le hn' hvl
  have hmc := makeCost_mono (a := truncNeed ql (E j)) (b := 2 * NW n + 2)
    (by unfold truncNeed; exact Nat.le_trans (Nat.min_le_left _ _) hql) (by omega)
  clear hvl
  exact k2 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc' (hex _ hsl) (zs_keep hsl hsp0 hzs) (hzv2.trans hzv) hl0 hl e0 e1 e2 (by rw [hv', hv]) hn'
    hlen (bud_step hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callT1 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkc : 4608 ≤ kc) (hkT : stkT ≤ kc)
    (haT : aboveT ≤ 88) (i : Nat) (hi300 : i < 300) (hpcv : pcv = 1797104 + 4 * i)
    (k2 : S2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hv : natVal M q ql = Zv * Zv) (hnq : NatNorm M q ql) (hql : ql ≤ 2 * NW n + 2)
    (hb : b - spent sqrC mulC n j - P1 sqrC n ≤ b1) (hE : E j ≤ 64 * NW n)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1786000) (h30 : S'.regs 30 = BitVec.ofNat 64 pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h1 : S'.regs 1 = BitVec.ofNat 64 ql) (h2 : S'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : S'.regs 3 = BitVec.ofNat 64 q) (h4 : S'.regs 4 = BitVec.ofNat 64 ql) (h5 : S'.regs 5 = BitVec.ofNat 64 qc)
    (h6 : S'.regs 6 = BitVec.ofNat 64 (E j)) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S' (GoalQ R kc sqrC mulC b L zp zc st xp xl n s) := by
  subst hpcv
  have hnw : NW n ≤ 2 ^ 12 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hq64 : q < 2 ^ 64 := hmid.2.2.2.1.2.1
  have hqc40 : qc < 2 ^ 40 := hmid.2.2.2.1.1
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  refine truncCall2 hap hns htr (b := b1) (L := L1) (zp := q) (zl := ql) (zc := qc) (x := q) (xl := ql) (xc := qc)
    (n := E j) (ra_mi hap hnf i hi300) (by rw [hpc]; rfl) h30 h0 h1 h2 h3 h4 h5 h6 hq64 (by omega) (by omega) hq64
    (by omega) (by omega) (by omega)
    (truncPre_at hpre hmid hsp h28 hm hkT haT (by omega) (by omega)
      (bud_ok hb hbud (m := makeCost (2 * NW n + 2)) (by simp only [roundCost, P1]; omega)
        (makeCost_mono (by unfold truncNeed; exact Nat.le_trans (Nat.min_le_left _ _) hql) (by omega))))
    (Or.inl (by rw [hm]; exact hnq)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost => postT1 hkc hkT haT k2 hpre hn hmid hj1 hjn hbud hcong hex hzs
      hzv hl0 hl hv hql hb hE hsp h28 h18 hm hpc' hsp' h28' h18' hreg' hpost

/-! ## second `zz.trunc(zz, e)`: `S3`'s facts → `S4` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem postT2 (hkc : 4608 ≤ kc) {stkT aboveT : Nat} (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (k2 : S4 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hv : natVal M q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl)) (hql : ql ≤ 2 * NW n)
    (hb : b - spent sqrC mulC n j - P3 sqrC mulC n ≤ b1) (hE : E j ≤ 64 * NW n)
    {S' s' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc' : s'.pc = BitVec.ofNat 64 pcv) (hsp' : s'.sp = S'.sp) (h28' : s'.regs 28 = S'.regs 28)
    (h18' : s'.regs 18 = S'.regs 18) (hreg : s'.mem.regions = S'.mem.regions)
    (hpost : TruncPost R b1 L1 stkT aboveT q qc q ql (E j) S' s') :
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨q', ql', qc', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hreuse, -⟩, -, ⟨hLE, hbud', hinv'⟩,
    hF', hLF'⟩ := hpost
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  obtain ⟨hq1, hq2⟩ := hreuse (by unfold truncNeed; omega)
  subst q' qc'
  have hS' := sp'_eq hsp
  rw [hm] at hF' hLF' hreg hv'
  rw [h28] at hinv'
  obtain ⟨hF2, hLF2, hsb, -, -⟩ := nostk hpre hmid.2.1 hS' hkT haT hmid.2.2.2.1 hF' hLF' hLE
  obtain ⟨mid2, hzv2, hsl⟩ := after_zz hpre hkc hmid hS' hkT haT hreg hF2 hLF2 hLE hinv' hsb hlive' hc40'
    hmid.2.2.2.1.2.1 (Or.inl ⟨rfl, rfl⟩) (fun h => absurd ⟨rfl, rfl⟩ h) hlc' hmid.2.2.2.2.2.2.2.2
  have hsp0 : 240 ≤ s.sp.toNat := by have := sp_K hpre; omega
  have hvl : natVal s'.mem q ql' < 2 ^ (64 * NW n) := by
    rw [hv']; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) hE)
  have hlen : ql' ≤ NW n := len_le hn' hvl
  have hmc := makeCost_mono (a := truncNeed ql (E j)) (b := 2 * NW n + 2)
    (by unfold truncNeed; exact Nat.le_trans (Nat.min_le_left _ _) (by omega)) (by omega)
  clear hvl
  exact k2 s' j p l c q ql' qc L' b' Zv ⟨⟨hpre⟩, hn, hsp'.trans hsp, h28'.trans h28, h18'.trans h18, ⟨mid2⟩, hj1,
    hjn, hbud, hcong⟩ hpc' (hex _ hsl) (zs_keep hsl hsp0 hzs) (hzv2.trans hzv) hl0 hl e0 e1 e2 (by rw [hv', hv]) hn'
    hlen (bud_step hb hbud' hmc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callT2 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkc : 4608 ≤ kc) (hkT : stkT ≤ kc)
    (haT : aboveT ≤ 88) (i : Nat) (hi300 : i < 300) (hpcv : pcv = 1797104 + 4 * i)
    (k2 : S4 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s pcv Ex E Kx)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {j p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 Zv : Nat} {M : Memory}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hbud : spent sqrC mulC n j + roundCost sqrC mulC n ≤ b)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hex : ∀ M', SlotsKept s M M' → Ex j M') (hzs : ZS s M p l c) (hzv : natVal M p l = Zv) (hl0 : 0 < l)
    (hl : l ≤ NW n + 1) (hv : natVal M q ql = Zv * Zv % 2 ^ E j * natVal s.mem xp (min (Kx j) xl)) (hnq : NatNorm M q ql) (hql : ql ≤ 2 * NW n)
    (hb : b - spent sqrC mulC n j - P3 sqrC mulC n ≤ b1) (hE : E j ≤ 64 * NW n)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28)
    (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1786000) (h30 : S'.regs 30 = BitVec.ofNat 64 pcv)
    (h0 : S'.regs 0 = BitVec.ofNat 64 q) (h1 : S'.regs 1 = BitVec.ofNat 64 ql) (h2 : S'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : S'.regs 3 = BitVec.ofNat 64 q) (h4 : S'.regs 4 = BitVec.ofNat 64 ql) (h5 : S'.regs 5 = BitVec.ofNat 64 qc)
    (h6 : S'.regs 6 = BitVec.ofNat 64 (E j)) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S' (GoalQ R kc sqrC mulC b L zp zc st xp xl n s) := by
  subst hpcv
  have hnw : NW n ≤ 2 ^ 12 := by have := hpre.2.2.2.2.1; simp only [NW]; omega
  have hq64 : q < 2 ^ 64 := hmid.2.2.2.1.2.1
  have hqc40 : qc < 2 ^ 40 := hmid.2.2.2.1.1
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  refine truncCall2 hap hns htr (b := b1) (L := L1) (zp := q) (zl := ql) (zc := qc) (x := q) (xl := ql) (xc := qc)
    (n := E j) (ra_mi hap hnf i hi300) (by rw [hpc]; rfl) h30 h0 h1 h2 h3 h4 h5 h6 hq64 (by omega) (by omega) hq64
    (by omega) (by omega) (by omega)
    (truncPre_at hpre hmid hsp h28 hm hkT haT (by omega) (by omega)
      (bud_ok hb hbud (m := makeCost (2 * NW n + 2)) (by simp only [roundCost, P3, P2, P1]; omega)
        (makeCost_mono (by unfold truncNeed; exact Nat.le_trans (Nat.min_le_left _ _) (by omega)) (by omega))))
    (Or.inl (by rw [hm]; exact hnq)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost => postT2 hkc hkT haT k2 hpre hn hmid hj1 hjn hbud hcong hex hzs
      hzv hl0 hl hv hql hb hE hsp h28 h18 hm hpc' hsp' h28' h18' hreg' hpost

end

end FvModexp.Arm64.ModInv
