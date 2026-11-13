import FvModexp.Proofs.Arm64.ExpQ.SlowSqQ
import FvModexp.Proofs.Arm64.Exp.SlowL1

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowU1.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): lower-loop segment U1 — `T1` (`j < w`) → `zz = zz.sqr(stk, z)` → `KS2` (agent expmc)

`T1` (`fnE + 0x3d8`): `CMP R14, R13; BGE` (not taken), stores `128 := z.cap`, `120 := z.len`, `336 := z.ptr`,
`208 := j`, `168 := r.len`, `352 := r.ptr`, `192 := q.cap`, `184 := q.len`, `360 := q.ptr`, `176 := r.cap`,
`160 := v`, the argument moves and `CALL nat.sqr` (return `fnE + 0x424`, index 149).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `sqr` call from the stores' memory (pure; `T` = the call state) -/
theorem callL1Q {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {sqC : Nat → Nat} {H : Nat} (hsq : SqrHypGQ impl R ns stkS aboveS sqC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S0 : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S0 L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (hjw : j < 64) (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : sqC zl + stkR H S0.mem st ≤ b1)
    (KS : ∀ (S : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat),
      KS2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L2 b2 j w v p' l' c' (Zv * Zv) z zl zc'
        r rl rc q ql qc → b1 - (sqC zl + stkR H S0.mem st) + stkR H S.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 S Q)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1815584) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = BitVec.ofNat 64 (sp - 8)) (h18 : T.regs 18 = r18)
    (hF : MemFrame S0.mem T.mem (wsL1 sp)) (hrg : T.mem.regions = S0.mem.regions)
    (r240 : T.mem.readLE (sp + 240) 8 = zc') (r248 : T.mem.readLE (sp + 248) 8 = zl)
    (r384 : T.mem.readLE (sp + 384) 8 = z) (r200 : T.mem.readLE (sp + 200) 8 = j)
    (r264 : T.mem.readLE (sp + 264) 8 = rl) (r392 : T.mem.readLE (sp + 392) 8 = r)
    (r272 : T.mem.readLE (sp + 272) 8 = qc) (r280 : T.mem.readLE (sp + 280) 8 = ql)
    (r400 : T.mem.readLE (sp + 400) 8 = q) (r256 : T.mem.readLE (sp + 256) 8 = rc)
    (r160 : T.mem.readLE (sp + 160) 8 = v.toNat)
    (h30 : T.regs 30 = BitVec.ofNat 64 (1788352 + 4 * 265))
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h1 : T.regs 1 = BitVec.ofNat 64 zzl) (h2 : T.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 z) (h5 : T.regs 5 = BitVec.ofNat 64 zl)
    (h6 : T.regs 6 = BitVec.ofNat 64 zc') :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T T.mem L1 b1 :=
    JC.frameW hP hk.jc (wsL1_in sp) hF hrg hsp h28 h29 h18
  have hB := BB.frameW hP (wsL1_in sp) hF hk.bb
  have hs13 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz := hk.zl128
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hw63 := hk.w63
  have r216 : T.mem.readLE (sp + 216) 8 = w := by
    rw [hF.readLE _ _ (by simp only [wsL1, outside_cons, outside_nil, and_true]; omega)]; exact hk.s216
  have eR := stkRW hP (wsL1_in sp) hF H
  refine sqrSQ hap hns hnf hsq hkS haS hP hj hB (by omega) (by omega) (lvl_sq hz hH) (by rw [eR]; exact hcost) (idx := 265)
    (by decide) hpc h30 h0 h1 h2 h3 h4 h5 h6 fun s' L2 b2 p' l' c' hpc' hj' hkp e0 e1 e2 hB' hl' hbud =>
    KS s' L2 b2 p' l' c' ?_ (by rw [eR] at hbud; exact hbud)
  have hr : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 424 → s'.mem.readLE a 8 = T.mem.readLE a 8 :=
    fun a h1 h2 => hkp a 8 (Or.inr ⟨h1, by omega⟩)
  exact ⟨hpc', hj', hB', by omega, hjw, hw63, (hr _ (by omega) (by omega)).trans r216, e0, e1, e2,
    (hr _ (by omega) (by omega)).trans r384, (hr _ (by omega) (by omega)).trans r248,
    (hr _ (by omega) (by omega)).trans r240, (hr _ (by omega) (by omega)).trans r392,
    (hr _ (by omega) (by omega)).trans r264, (hr _ (by omega) (by omega)).trans r256,
    (hr _ (by omega) (by omega)).trans r400, (hr _ (by omega) (by omega)).trans r280,
    (hr _ (by omega) (by omega)).trans r272, (hr _ (by omega) (by omega)).trans r200,
    (hr _ (by omega) (by omega)).trans r160⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **U1**: from `KT2` with `j < w` -/
theorem segL1Q {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {sqC : Nat → Nat} {H : Nat} (hsq : SqrHypGQ impl R ns stkS aboveS sqC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (hjw : j < 64) (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : sqC zl + stkR H S.mem st ≤ b1)
    (KS : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat),
      KS2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L2 b2 j w v p' l' c' (Zv * Zv) z zl zc'
        r rl rc q ql qc → b1 - (sqC zl + stkR H S.mem st) + stkR H S'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : S.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hk.jc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hjw' := hjw
  have hw63 := hk.w63
  have hjc := hk.jc
  have hk' := hk
  have epc := hk.pc; have e0 := hk.e0; have e5 := hk.e5; have e2 := hk.e2; have e24 := hk.e24
  have e23 := hk.e23; have e22 := hk.e22; have e20 := hk.e20; have e15 := hk.e15; have e19 := hk.e19
  have e21 := hk.e21; have e17 := hk.e17; have e16 := hk.e16; have e13 := hk.e13; have e9 := hk.e9
  have e3 := hk.e3
  have esp := hjc.esp; have e28 := hjc.e28; have e29 := hjc.e29; have e18 := hjc.e18
  clear hjc
  have hB := hk'.bb
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨br, brc⟩ := hB.br.lt64
  obtain ⟨bq, bqc⟩ := hB.bq.lt64
  have bzl := hB.bz.2.1
  have bzzl := hB.lzz
  have brl := hB.lr
  have bql := hB.lq
  clear hB
  janus_run [hmacc] until [1815584]
  refine callL1Q hap hns hnf hsq hkS haS hP hk' hjw' hH hcost KS _ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case hF => simp only [wsL1]; janus_frame
  case hrg => simp only [Memory.regions_writeLE]
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.Q.ExpSlow
