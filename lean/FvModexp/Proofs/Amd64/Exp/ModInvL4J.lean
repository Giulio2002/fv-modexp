import FvModexp.Proofs.Amd64.Exp.ModInvL4

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S4 → S5` compositions (agent infra s58)

`segL4` (loop) and `segF5a` (final): the run (`ModInvL4`), the round facts at the callee's entry memory (`mid_st`),
then `callLsh`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem p5_le {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {xl n j k : Nat} :
    P4 sqrC mulC xl n j k + makeCost (NW n + 2) ≤ roundCost sqrC mulC xl n j k := by
  simp only [roundCost, P4, P3, P2, P1]; omega

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the shared composition: `Ex` is kept by the spills (`hexw`) and by the callee (`hexk`) -/
theorem seg4 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) {Ex : Nat → Memory → Prop} {E Kx : Nat → Nat}
    (pc i : Nat) (hi : i < 0x610)
    (hrun : ∀ (ra : W64) (Qp : State → Prop) (sp p l c q ql qc : Nat), 232 ≤ sp → sp ≤ 2 ^ 48 → q < 2 ^ 64 →
      ql < 2 ^ 64 → qc < 2 ^ 64 → ∀ S : State, S.rip = BitVec.ofNat 64 pc →
      S.regs 4 = BitVec.ofNat 64 (sp - 224) → S.mem.accessible (sp - 232) 232 true = true →
      S.mem.readLE (sp - 224 + 208) 8 = p → S.mem.readLE (sp - 224 + 176) 8 = l →
      S.mem.readLE (sp - 224 + 184) 8 = c →
      S.regs 0 = BitVec.ofNat 64 q → S.regs 3 = BitVec.ofNat 64 ql → S.regs 1 = BitVec.ofNat 64 qc →
      (∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Lsh.fn) →
        S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
        S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
        S'.regs 0 = BitVec.ofNat 64 p → S'.regs 3 = BitVec.ofNat 64 l → S'.regs 1 = BitVec.ofNat 64 c →
        S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
        S'.regs 9 = BitVec.ofNat 64 1 →
        S'.mem = (((S.mem.writeLE (sp - 224 + 200) 8 q).writeLE (sp - 224 + 104) 8 ql).writeLE (sp - 224 + 112) 8
          qc).writeLE (sp - 224 - 8) 8 (0x5ea8c0 + i) →
        ReachesRet (LibW.program.link impl) ra S' Qp) →
      ReachesRet (LibW.program.link impl) ra S Qp)
    (hexw : ∀ j (M : Memory) a v, 232 ≤ (s.regs 4).toNat → (s.regs 4).toNat - 232 ≤ a → a + 8 ≤ (s.regs 4).toNat - 104 ∨
      (s.regs 4).toNat - 24 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 16 → Ex j M → Ex j (M.writeLE a 8 v))
    (hexk : ∀ j (M M' : Memory), 232 ≤ (s.regs 4).toNat → SlotsKept s M M' → Ex j M → Ex j M')
    (k5 : S5 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s (0x5ea8c0 + i) Ex E Kx) :
    S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s pc Ex E Kx := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hzs hzv hl0 hl h0 h3 h1 hv hN hql hb
  have hrc' := hrc
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc'
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) 232 true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hq : q < 2 ^ 64 := hmid.2.2.2.1.2.1
  have hqc : qc < 2 ^ 40 := hmid.2.2.2.1.1
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  have hl1 : l ≤ NW n + 1 := Nat.le_trans hl (zB_le hjn)
  obtain ⟨z1, z2, z3⟩ := hzs
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine hrun _ _ (s.regs 4).toNat p l c q ql qc (by omega) (by omega) hq (by omega) (by omega) S hpc h4 hacc
    (by rw [show (s.regs 4).toNat - 224 + 208 = (s.regs 4).toNat - 16 by omega]; exact z1)
    (by rw [show (s.regs 4).toNat - 224 + 176 = (s.regs 4).toNat - 48 by omega]; exact z2)
    (by rw [show (s.regs 4).toNat - 224 + 184 = (s.regs 4).toNat - 40 by omega]; exact z3) h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 em
  obtain ⟨m1, v1, w1, -, n1, c1⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224 + 200) q (by omega) (by omega)
  obtain ⟨m2, v2, w2, -, n2, c2⟩ := mid_st hpre m1 (a := (s.regs 4).toNat - 224 + 104) ql (by omega) (by omega)
  obtain ⟨m3, v3, w3, -, n3, c3⟩ := mid_st hpre m2 (a := (s.regs 4).toNat - 224 + 112) qc (by omega) (by omega)
  obtain ⟨m4, v4, w4, -, n4, c4⟩ := mid_st hpre m3 (a := (s.regs 4).toNat - 224 - 8) (0x5ea8c0 + i) (by omega)
    (by omega)
  rw [← em] at m4 v4 w4 n4 c4
  have ex4 : Ex j S'.mem := by
    rw [em]
    exact hexw _ _ _ _ (by omega) (by omega) (Or.inl (by omega)) (hexw _ _ _ _ (by omega) (by omega) (Or.inl (by omega))
      (hexw _ _ _ _ (by omega) (by omega) (Or.inl (by omega)) (hexw _ _ _ _ (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩) hex)))
  have qs4 : QS s S'.mem q ql qc := by
    rw [em]
    refine ⟨?_, ?_, ?_⟩
    · rw [slot_other (by omega), slot_other (by omega), slot_other (by omega),
        show (s.regs 4).toNat - 24 = (s.regs 4).toNat - 224 + 200 by omega, slot_self hq]
    · rw [slot_other (by omega), slot_other (by omega),
        show (s.regs 4).toNat - 120 = (s.regs 4).toNat - 224 + 104 by omega, slot_self (by omega)]
    · rw [slot_other (by omega), show (s.regs 4).toNat - 112 = (s.regs 4).toNat - 224 + 112 by omega,
        slot_self (by omega)]
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5ea8c0 + i := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by omega)]
  have hm : makeCost (l + 1 / 64 + 1) ≤ makeCost (NW n + 2) := makeCost_mono (by omega) (by omega)
  refine callLsh hap hns hnf hls hkL haL i hi hpre hx0 hdf0 m4 hl0 hl1 (bud_okP hb hbud p5_le hm) e4 (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd r0 r3 r1 r7 r6 r8 r9 ?_
  intro s' L' b' p' l' c' hpc' hsp' h5' habi' mid' hsl hqw f0 f3 f1 hv' hN' hll hbud' hstk
  refine k5 s' j p' l' c' q ql qc L' b' Zv ⟨⟨hpre⟩, hn, hsp', h5', habi', ⟨mid'⟩, hj1, hjn, hbud, hcong⟩ hpc'
    (hexk _ _ _ (by omega) hsl ex4) (qs_keep hsl (by omega) qs4) f0 f3 f1 (by rw [hv', v4, v3, v2, v1, hzv]) hN' (by omega)
    (by simp only [natVal]; rw [hqw ql hqlc]; exact (w4.trans (w3.trans (w2.trans (w1.trans hv)))))
    (norm_keep hqw hqlc (n4 (n3 (n2 (n1 hN))))) hql ?_
  rw [hstk, stkR_congr c4, stkR_congr c3, stkR_congr c2, stkR_congr c1]
  exact bud_stepP hb hbud p5_le hbud' hm


theorem segL4 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (J : Nat)
    (k5 : S5 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204729 (ExL3 s n J) eL kL) :
    S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204667 (ExL3 s n J) eL kL :=
  seg4 hap hns hnf hls hkL haL hx0 hdf0 6204667 1145 (by decide) (runL4 impl)
    (fun _ _ _ _ h0 h1 h2 h => ⟨(slot_other (by omega)).trans h.1, (slot_other (by omega)).trans h.2.1, h.2.2⟩)
    (fun _ _ _ h0 hk h => ⟨slot_keep hk h0 (by decide) (by decide) h.1,
      slot_keep hk h0 (by decide) (by decide) h.2.1, h.2.2⟩) k5

theorem segF5a (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (k5 : S5 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6205081 (ExF n) (eF n) (kF n)) :
    S4 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6205019 (ExF n) (eF n) (kF n) :=
  seg4 hap hns hnf hls hkL haL hx0 hdf0 6205019 1497 (by decide) (runF5a impl)
    (fun _ _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) k5

end

end FvModexp.Amd64.ModInv
