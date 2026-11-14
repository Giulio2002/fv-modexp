import FvModexp.Proofs.Amd64.Exp.SlowMu
import FvModexp.Proofs.Amd64.Exp.SlowU2R

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): upper-loop segment U2 — `KS1` → (`v` bit 63 set: `zz = zz.mul(stk, z, x)`) → `KD1`
(agent expmc s81; twin of arm64 `SlowU2Q`)

Bit clear (`runU2`, `KN`): `zz` (the old `z`) reloaded into `(R8, SI, DI)`, `z` kept. Bit set (`KM`): `mulS` (return
`ml1R`), then `runU2b`: `z` := the product, `zz` := the old `z` (slots `0x180/0x118/0x120`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem wsU2_own {sp K : Nat} (hK : K + 8 ≤ sp) : ∀ r ∈ wsU2 sp, OwnR sp K r := by
  intro r hr
  simp only [wsU2, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega

/-- the slots U2's stores keep -/
theorem rdU2 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' (wsU2 sp)) (h8 : 8 ≤ sp) :
    (∀ a k, sp + 0x18 ≤ a → a + k ≤ sp + 0x118 → m'.readLE a k = m.readLE a k) ∧
    (∀ a k, sp + 0x128 ≤ a → a + k ≤ sp + 0x180 → m'.readLE a k = m.readLE a k) ∧
    (∀ a k, sp + 0x188 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨fun a k h1 h2 => hF.readLE _ _ ?_, fun a k h1 h2 => hF.readLE _ _ ?_, fun a k h1 h2 => hF.readLE _ _ ?_⟩ <;>
  simp only [wsU2, outside_cons, outside_nil, and_true] <;> omega

theorem muW {zl xl W : Nat} (hz : zl ≤ 256) (hx : xl ≤ 128) (hW : 21072 ≤ W) : mulW64 zl xl ≤ W := by
  unfold mulW64
  have hl : Nat.log2 (zl * xl) ≤ 15 := by
    rcases Nat.eq_zero_or_pos (zl * xl) with h | h
    · rw [h]; decide
    · have hm : zl * xl ≤ 256 * 128 := Nat.mul_le_mul hz hx
      have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 h)).2 (show zl * xl < 2 ^ 16 by omega)
      omega
  split <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **U2**: `KS1` → `KD1` (the optional `mul`) -/
theorem segU2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} (hml : Q.DivRec.MulHypQE impl R ns W) (hWK : W ≤ K) (hW : 21072 ≤ W)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : NHyp.XFacts R L xp xl xc) (hxl0 : 0 < xl)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KS1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 j w v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : mulCQ zl xl + stkR H S.mem st ≤ b1)
    (KD : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 z' zl' zc'' zz' zzl' zzc' : Nat),
      KD1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 j w v z' zl' zc''
        (if v.getLsbD 63 = true then Zv * natVal s.mem xp xl else Zv) zz' zzl' zzc' rr rl rc q ql qc →
      b1 - ((if v.getLsbD 63 = true then mulCQ zl xl else 0) + stkR H S.mem st) + stkR H S'.mem st ≤ b2 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml8 : ml ≤ 128 := hP.2.2.2.2.2.1
  have hs13 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hacc : ∀ M : Memory, (∀ a n w, M.accessible a n w = s.mem.accessible a n w) →
      M.accessible (sp - 8) 0x228 true = true := fun M hM => by
    rw [hM]; exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  have hzlb := hk.zlb
  obtain ⟨bz, bzc⟩ := hk.bb.bz.1.lt64
  have hzlc := hk.bb.bz.2.1
  have hsl := hk.jc.esl
  obtain ⟨-, -, -, -, -, -, -, -, -, sl200, sl208, sl210, sl218⟩ := hsl
  refine runU2 ret0 Q sp z zl zc' zz zzl zzc xp xl xc st v S.mem (hacc _ hk.jc.wc.fr.accessible) (by omega) hK5
    bz (by omega) bzc hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hk.s88 hk.s128 hk.s130 hk.s188 sl208 sl210 sl218 sl200 S hk.pc hk.jc.esp rfl hk.e0 hk.e3 hk.e1
    ?_ ?_
  · intro T hb tpc t4 tm t0 t3 t1 t8 t6 t7 t2 t14 tfs tx tdf
    have hj := hk.jc.call (S' := T) (t4.trans hk.jc.esp.symm) t14 tfs tx tdf (by rw [tm]; exact hk.jc.wc)
      (fun a k _ _ => by rw [tm])
    have hB := hk.bb
    rw [← tm] at hB
    refine KD T L1 b1 z zl zc' zz zzl zzc ⟨hj, by rw [if_neg (by rw [hb]; decide)]; exact hB, hk.w63, by rw [tm]; exact hk.s138, tpc,
      by omega, hk.jw, t0, t3, t1, t8, t6, t7, t2, by rw [tm]; exact hk.s160, by rw [tm]; exact hk.s90,
      by rw [tm]; exact hk.s98, by rw [tm]; exact hk.s168, by rw [tm]; exact hk.sa0, by rw [tm]; exact hk.sa8,
      by rw [tm]; exact hk.sb8, by rw [tm]; exact hk.s88⟩ ?_
    rw [if_neg (by rw [hb]; decide), Nat.zero_add, tm]
    omega
  · intro T hb tpc t4 t14 tfs tx tdf tF trg tra w120 w180 w118 y0 y1 y2 r0 r3 r1 r7 r6 r8 r9
    obtain ⟨uA, uB, uC⟩ := rdU2 tF (by omega)
    refine mulS hap hns hnf hml hWK hP hk.jc hk.bb hX hxl0 (by omega) (muW (by omega) hxl hW) (by omega) (by omega)
      hcost (idx := 0x37d) (by decide) T tpc t4 t14 tfs tx tdf tF trg (wsU2_own hK3)
      (fun a k h1 h2 => uC a k (by omega) h2) tra r0 r3 r1 r7 r6 r8 r9 y0 y1 y2 ?_
    intro s' L2 b2 p' l' c' hpc' hj' hkp e0 e3 e1 hB' hl' hbud
    have rA : ∀ a, sp + 0x68 ≤ a → a + 8 ≤ sp + 0x118 → s'.mem.readLE a 8 = S.mem.readLE a 8 :=
      fun a h1 h2 => (hkp a 8 h1 (by omega)).trans (uA a 8 (by omega) h2)
    have rB : ∀ a, sp + 0x128 ≤ a → a + 8 ≤ sp + 0x180 → s'.mem.readLE a 8 = S.mem.readLE a 8 :=
      fun a h1 h2 => (hkp a 8 (by omega) (by omega)).trans (uB a 8 h1 h2)
    refine runU2b ret0 Q sp zl zc' z v s'.mem (hacc _ hj'.wc.fr.accessible) (by omega) hK5
      ((rA _ (by omega) (by omega)).trans hk.s88) ((hkp _ 8 (by omega) (by omega)).trans w118)
      ((hkp _ 8 (by omega) (by omega)).trans w120) ((hkp _ 8 (by omega) (by omega)).trans w180) s' hpc' hj'.esp rfl
      ?_
    intro T2 t2pc t24 t2m t20 t23 t21 t28 t26 t27 t22 t214 t2fs t2x t2df
    have hj2 := hj'.call (S' := T2) (t24.trans hj'.esp.symm) t214 t2fs t2x t2df (by rw [t2m]; exact hj'.wc)
      (fun a k _ _ => by rw [t2m])
    rw [← t2m] at hB' rA rB
    refine KD T2 L2 b2 p' l' c' z zl zc' ⟨hj2, by rw [if_pos hb]; exact hB', hk.w63,
      (rB _ (by omega) (by omega)).trans hk.s138, t2pc, by omega, hk.jw, t20.trans e0, t23.trans e3, t21.trans e1,
      t28, t26, t27, t22, (rB _ (by omega) (by omega)).trans hk.s160, (rA _ (by omega) (by omega)).trans hk.s90,
      (rA _ (by omega) (by omega)).trans hk.s98, (rB _ (by omega) (by omega)).trans hk.s168,
      (rA _ (by omega) (by omega)).trans hk.sa0, (rA _ (by omega) (by omega)).trans hk.sa8,
      (rA _ (by omega) (by omega)).trans hk.sb8, (rA _ (by omega) (by omega)).trans hk.s88⟩ ?_
    rw [if_pos hb, t2m]
    exact hbud

end

end FvModexp.Amd64.ExpSlow
