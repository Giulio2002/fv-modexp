import FvModexp.Proofs.Amd64.Exp.SlowMu
import FvModexp.Proofs.Amd64.Exp.SlowK2
import FvModexp.Proofs.Amd64.Exp.SlowL2R
import FvModexp.Proofs.Amd64.Exp.SlowXU

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): lower-loop segment L2 — `KS2` → (`zz = zz.mul(stk, z, x)` if bit 63 of `v`) → `KD2`
(agent asm s75; twin of arm64 `SlowL2Q`; nat.go:773-776)

Bit clear: `runL2` straight to `fnE + 0x6b3` (`z` = the square, `zz` = the old `z`). Bit set: `runL2` → expmc's
`mulS` (return `ml2R`) → `runL2b`: `z` = the product, `zz` = the square.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem wsL2_own {sp K : Nat} (hK : K + 8 ≤ sp) : ∀ r ∈ wsL2 sp, OwnR sp K r := by
  intro r hr
  simp only [wsL2, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega

/-- the slots L2 does not write before `nat.mul` -/
theorem rdL2 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' (wsL2 sp)) (h8 : 8 ≤ sp) :
    m'.readLE (sp + 0xc0) 8 = m.readLE (sp + 0xc0) 8 ∧ m'.readLE (sp + 0xb0) 8 = m.readLE (sp + 0xb0) 8 ∧
    m'.readLE (sp + 0x160) 8 = m.readLE (sp + 0x160) 8 ∧ m'.readLE (sp + 0xf0) 8 = m.readLE (sp + 0xf0) 8 ∧
    m'.readLE (sp + 0xe8) 8 = m.readLE (sp + 0xe8) 8 ∧ m'.readLE (sp + 0x168) 8 = m.readLE (sp + 0x168) 8 ∧
    m'.readLE (sp + 0x100) 8 = m.readLE (sp + 0x100) 8 ∧ m'.readLE (sp + 0xf8) 8 = m.readLE (sp + 0xf8) 8 ∧
    m'.readLE (sp + 0x88) 8 = m.readLE (sp + 0x88) 8 ∧
    (∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_,
    hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, fun a k h1 _ => hF.readLE _ _ ?_⟩ <;>
  simp only [wsL2, outside_cons, outside_nil, and_true] <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **L2**: from `KS2` to `KD2` (`z := z · x` when bit 63 of `v` is set) -/
theorem segL2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} (hml : Q.DivRec.MulHypQE impl R ns W) (hWK : W ≤ K) (hW : mulWX64 ≤ W)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 i j : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KS2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i j v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : mulCQ zl xl + stkR H S.mem st ≤ b1)
    (KD : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 z' zl' zc'' zz' zzl' zzc' : Nat),
      KD2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 i j v z' zl' zc''
        (if v.getLsbD 63 = true then Zv * natVal s.mem xp xl else Zv) zz' zzl' zzc' rr rl rc q ql qc →
      b1 - ((if v.getLsbD 63 = true then mulCQ zl xl else 0) + stkR H S.mem st) + stkR H S'.mem st ≤ b2 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmlb : ml ≤ 128 := hP.2.2.2.2.2.1
  have hs13 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hk.jc.wc.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  obtain ⟨bz, bzc⟩ := hk.bb.bz.1.lt64
  have hzl := hk.bb.bz.2.1
  have hzlb := hk.zlb
  obtain ⟨-, -, -, -, -, -, -, -, -, e200, e208, e210, e218⟩ := hk.jc.esl
  have bxp := readLE_lt_8 S.mem (sp + 0x208)
  have bxl := readLE_lt_8 S.mem (sp + 0x210)
  have bxc := readLE_lt_8 S.mem (sp + 0x218)
  refine runL2 ret0 Q sp z zl zc' zz zzl zzc xp xl xc st v S.mem hacc (by omega) hK5 bz (by omega) bzc
    (by omega) (by omega) (by omega) hk.s88
    hk.se0 hk.sd8 hk.s170 e208 e210 e218 e200 S hk.pc hk.jc.esp rfl hk.e0 hk.e3 hk.e1 ?_ ?_
  · intro T hbit t1 t4 tm r0 r3 r1 r8 r6 r7 r2 t14 tfs tx tdf
    have hjc := hk.jc.keepM tm (t4.trans hk.jc.esp.symm) t14 tfs tx tdf
    have hne : ¬ (v.getLsbD 63 = true) := Bool.eq_false_iff.mp hbit
    refine KD T L1 b1 z zl zc' zz zzl zzc ?_ ?_
    · rw [if_neg hne]
      exact ⟨hjc, by rw [tm]; exact hk.bb, hk.iy, by rw [tm]; exact hk.sc0, by rw [tm]; exact hk.sb0, t1,
        by omega, hk.jw, r0, r3, r1, r8, r6, r7, r2, by rw [tm]; exact hk.s160, by rw [tm]; exact hk.sf0,
        by rw [tm]; exact hk.se8, by rw [tm]; exact hk.s168, by rw [tm]; exact hk.s100, by rw [tm]; exact hk.sf8,
        by rw [tm]; exact hk.s88⟩
    · rw [if_neg hne, tm]; omega
  · intro T hbit t1 t4 t14 tfs tx tdf tF trg tra wd0 w1a0 wc8 wy0 wy1 wy2 r0 r3 r1 r7 r6 r8 r9
    obtain ⟨uc0, ub0, u160, uf0, ue8, u168, u100, uf8, u88, ukw⟩ := rdL2 tF (by omega)
    have hz12 : zl ≤ 2 ^ 12 := by omega
    have hs16 : stLen s.mem st + 4 * (zl + xl) + 64 ≤ 2 ^ 16 := by omega
    have hH' : stLen s.mem st + 4 * (zl + xl) + 64 ≤ H := by omega
    refine mulS hap hns hnf hml hWK hP hk.jc hk.bb hX hxl0 hz12 (Nat.le_trans (mulW64_le_X hz12 (by omega)) hW) hs16
      hH' hcost (idx := 0x693) (by decide) T t1 t4 t14 tfs tx tdf tF trg (wsL2_own hK3) ukw tra r0 r3 r1 r7 r6
      r8 r9 wy0 wy1 wy2 ?_
    intro s' L2 b2 p' l' c' hpc' hj' hkp e0 e3 e1 hB' hl' hbud
    have hr : ∀ a, sp + 0x68 ≤ a → a + 8 ≤ sp + 0x220 → s'.mem.readLE a 8 = T.mem.readLE a 8 :=
      fun a h1 h2 => hkp a 8 h1 h2
    refine runL2b ret0 Q sp zl zc' z v s'.mem
      (by rw [hj'.wc.fr.accessible]
          exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega))
      (by omega) hK5 ((hr _ (by omega) (by omega)).trans (u88.trans hk.s88))
      ((hr _ (by omega) (by omega)).trans wc8) ((hr _ (by omega) (by omega)).trans wd0)
      ((hr _ (by omega) (by omega)).trans w1a0) s' hpc' hj'.esp rfl ?_
    intro T2 q1 q4 qm q0 q3 q1' q8 q6 q7 q2 q14 qfs qx qdf
    have hjc := hj'.keepM qm (q4.trans hj'.esp.symm) q14 qfs qx qdf
    have hpos : v.getLsbD 63 = true := hbit
    refine KD T2 L2 b2 p' l' c' z zl zc' ?_ ?_
    · rw [if_pos hpos]
      have hrd : ∀ a, sp + 0x68 ≤ a → a + 8 ≤ sp + 0x220 → T2.mem.readLE a 8 = T.mem.readLE a 8 :=
        fun a h1 h2 => by rw [qm]; exact hr a h1 h2
      exact ⟨hjc, by rw [qm]; exact hB', hk.iy, (hrd _ (by omega) (by omega)).trans (uc0.trans hk.sc0),
        (hrd _ (by omega) (by omega)).trans (ub0.trans hk.sb0), q1, by omega, hk.jw, q0.trans e0, q3.trans e3,
        q1'.trans e1, q8, q6, q7, q2, (hrd _ (by omega) (by omega)).trans (u160.trans hk.s160),
        (hrd _ (by omega) (by omega)).trans (uf0.trans hk.sf0), (hrd _ (by omega) (by omega)).trans (ue8.trans hk.se8),
        (hrd _ (by omega) (by omega)).trans (u168.trans hk.s168),
        (hrd _ (by omega) (by omega)).trans (u100.trans hk.s100),
        (hrd _ (by omega) (by omega)).trans (uf8.trans hk.sf8), (hrd _ (by omega) (by omega)).trans (u88.trans hk.s88)⟩
    · rw [if_pos hpos, qm]; exact hbud

end

end FvModexp.Amd64.ExpSlow
