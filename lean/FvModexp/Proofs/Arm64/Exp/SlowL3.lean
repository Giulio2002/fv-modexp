import FvModexp.Proofs.Arm64.Exp.SlowK2
import FvModexp.Proofs.Arm64.Exp.SlowDv

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): lower-loop segment U3 — `KD2` → `zz, r = zz.div(stk, r, z, m)` → back-edge → `KT2`

At `JD` (`fnE + 0x484`): `R7 := len m` (slot 528), `CBNZ R7` (taken: `len m > 0`), stores `408 := z.ptr`,
`296 := z.len`, `288 := z.cap`, the argument moves and `CALL nat.div` (return `fnE + 0x4ec`, index 199); after it the
rotation `zz, r, q, z = q, z, zz, r` in registers, `JMP` to the back-edge `fnE + 0x1a4` (`v <<= 1`, `j++`, reloads)
and `T1` (`fnE + 0x3d8`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

/-- the slot stores of U3 -/
@[reducible] def wsL3 (sp : Nat) : List (Nat × Nat) :=
  [(sp + 368, sp + 368 + 8), (sp + 328, sp + 328 + 8), (sp + 320, sp + 320 + 8)]

theorem wsL3_in (sp : Nat) : InSlots sp (wsL3 sp) := by
  intro r hr
  simp only [wsL3, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega

set_option maxRecDepth 20000 in
/-- `KT2` at a state `T` with the memory of a state `S` carrying the context (pure) -/
theorem mkKT2 {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1)
    (hB : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc) (hzl : zl ≤ max xl ml) (hjw : j ≤ 64)
    (hw63 : w + 2 ≤ yl) (s216 : S.mem.readLE (sp + 216) 8 = w)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (fnE + 0x3d8)) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = BitVec.ofNat 64 (sp - 8)) (h18 : T.regs 18 = r18)
    (hm : T.mem = S.mem)
    (e0 : T.regs 0 = BitVec.ofNat 64 z) (e5 : T.regs 5 = BitVec.ofNat 64 zl) (e2 : T.regs 2 = BitVec.ofNat 64 zc')
    (e24 : T.regs 24 = BitVec.ofNat 64 zz) (e23 : T.regs 23 = BitVec.ofNat 64 zzl)
    (e22 : T.regs 22 = BitVec.ofNat 64 zzc) (e20 : T.regs 20 = BitVec.ofNat 64 r)
    (e15 : T.regs 15 = BitVec.ofNat 64 rl) (e19 : T.regs 19 = BitVec.ofNat 64 rc)
    (e21 : T.regs 21 = BitVec.ofNat 64 q) (e17 : T.regs 17 = BitVec.ofNat 64 ql)
    (e16 : T.regs 16 = BitVec.ofNat 64 qc) (e13 : T.regs 13 = BitVec.ofNat 64 j) (e9 : T.regs 9 = v)
    (e3 : T.regs 3 = BitVec.ofNat 64 st)
    (e7 : T.regs 7 = BitVec.ofNat 64 yp) (e8 : T.regs 8 = BitVec.ofNat 64 w) :
    KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc := by
  have hF : MemFrame S.mem T.mem [] := by rw [hm]; exact MemFrame.refl _ _
  have hrg : T.mem.regions = S.mem.regions := by rw [hm]
  rw [← hm] at hB s216
  exact ⟨hpc, JC.frameW hP hj (ws := []) (fun r hr => absurd hr List.not_mem_nil) hF hrg hsp h28 h29 h18,
    hB, hzl, hjw, hw63, s216, e0, e5, e2, e24, e23, e22, e20, e15, e19, e21, e17, e16, e13, e9, e3, e7, e8⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `div` call from the stores' memory, and the back-edge to `T1` (`T` = the call state) -/
theorem callL3 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {dvC : Nat → Nat → Nat → Nat} (hdv : DivHypLG impl R ns stkS aboveS dvC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hM : 0 < natVal s.mem mp ml)
    {ret0 : BitVec 64} {Q : State → Prop} {S0 : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KD2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S0 L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (hcost : dvC (stLen s.mem st) zl ml ≤ b1)
    (KT : ∀ (S : State) (L2 : List (Nat × Nat)) (b2 pq lq cq pr lr cr : Nat),
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L2 b2 (j + 1) w (v + v) pr lr cr
        (Zv % natVal s.mem mp ml) q ql qc z zl zc' pq lq cq → b1 - dvC (stLen s.mem st) zl ml ≤ b2 →
      ReachesRet (LibW.program.link impl) ret0 S Q)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1806848) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = BitVec.ofNat 64 (sp - 8)) (h18 : T.regs 18 = r18)
    (hF : MemFrame S0.mem T.mem (wsL3 sp)) (hrg : T.mem.regions = S0.mem.regions)
    (r368 : T.mem.readLE (sp + 368) 8 = z) (r328 : T.mem.readLE (sp + 328) 8 = zl)
    (r320 : T.mem.readLE (sp + 320) 8 = zc')
    (h30 : T.regs 30 = BitVec.ofNat 64 (1788352 + 4 * 315))
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h1 : T.regs 1 = BitVec.ofNat 64 zzl) (h2 : T.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 r) (h5 : T.regs 5 = BitVec.ofNat 64 rl)
    (h6 : T.regs 6 = BitVec.ofNat 64 rc) (h7 : T.regs 7 = BitVec.ofNat 64 z) (h8 : T.regs 8 = BitVec.ofNat 64 zl)
    (h9 : T.regs 9 = BitVec.ofNat 64 zc') (h10 : T.regs 10 = BitVec.ofNat 64 mp)
    (h11 : T.regs 11 = BitVec.ofNat 64 ml) (h12 : T.regs 12 = BitVec.ofNat 64 mc) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T T.mem L1 b1 :=
    JC.frameW hP hk.jc (wsL3_in sp) hF hrg hsp h28 h29 h18
  have hB := BB.frameW hP (wsL3_in sp) hF hk.bb
  have hs13 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hz := hk.zl384
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw63 := hk.w63
  have hjw := hk.jw
  have hrT : ∀ a, (a + 8 ≤ sp + 320 ∨ sp + 384 ≤ a ∧ a + 8 ≤ sp + 368 ∨ sp + 376 ≤ a) →
      T.mem.readLE a 8 = S0.mem.readLE a 8 :=
    fun a ha => hF.readLE _ _ (by simp only [wsL3, outside_cons, outside_nil, and_true]; omega)
  refine divS hap hns hnf hdv hkS haS hP hj hB hM (by omega) (by omega) hcost (idx := 315) (by decide) hpc h30
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 fun s' L2 b2 pq lq cq pr lr cr hpc' hj' hkp e0 e1 e2 e3 e4 e5 hB' hlr
      hbud => ?_
  have hr : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 544 → s'.mem.readLE a 8 = T.mem.readLE a 8 :=
    fun a h1 h2 => hkp a 8 (Or.inr ⟨h1, h2⟩)
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : s'.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hj'.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have q368 : s'.mem.readLE (sp + 368) 8 = z := (hr _ (by omega) (by omega)).trans r368
  have q328 : s'.mem.readLE (sp + 328) 8 = zl := (hr _ (by omega) (by omega)).trans r328
  have q320 : s'.mem.readLE (sp + 320) 8 = zc' := (hr _ (by omega) (by omega)).trans r320
  have q160 : s'.mem.readLE (sp + 160) 8 = v.toNat :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s160)
  have q200 : s'.mem.readLE (sp + 200) 8 = j :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s200)
  have q216 : s'.mem.readLE (sp + 216) 8 = w :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s216)
  have q400 : s'.mem.readLE (sp + 400) 8 = q :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s400)
  have q280 : s'.mem.readLE (sp + 280) 8 = ql :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s280)
  have q272 : s'.mem.readLE (sp + 272) 8 = qc :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s272)
  have hsf := hj'.sf
  have q464 := hsf.s464; have q496 := hsf.s496; have q504 := hsf.s504
  have hjs := hj'
  have esp := hjs.esp; have e28 := hjs.e28; have e29 := hjs.e29; have e18 := hjs.e18
  clear hjs hsf
  obtain ⟨bz, bzc⟩ := hB'.bz.1.lt64
  obtain ⟨bq, bqc⟩ := hB'.bq.lt64
  obtain ⟨brr, brc⟩ := hB'.br.lt64
  obtain ⟨bzz, bzzc⟩ := hB'.bzz.lt64
  have bzl := hB'.bz.2.1
  have bql := hB'.lq
  have brl := hB'.lr
  have bzzl := hB'.lzz
  have hv := v.isLt
  janus_run [hmacc] until [1789336]
  refine KT _ L2 b2 pq lq cq pr lr cr (mkKT2 hP hj' hB' (by omega) (by omega) hw63 q216 _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hbud
  all_goals (first | (janus_simp <;> omega) | (janus_simp; simp only [hk.s400, hk.s280, hk.s272, hk.s200, hk.s160,
    hk.s216, hk.jc.sf.s464, hk.jc.sf.s496, hk.jc.sf.s504, r368, r328, r320, ofNat_succ, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **U3**: from `KD2` through `div` and the back-edge to `T1` -/
theorem segL3 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {dvC : Nat → Nat → Nat → Nat} (hdv : DivHypLG impl R ns stkS aboveS dvC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hM : 0 < natVal s.mem mp ml)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KD2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (hcost : dvC (stLen s.mem st) zl ml ≤ b1)
    (KT : ∀ (S : State) (L2 : List (Nat × Nat)) (b2 pq lq cq pr lr cr : Nat),
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L2 b2 (j + 1) w (v + v) pr lr cr
        (Zv % natVal s.mem mp ml) q ql qc z zl zc' pq lq cq → b1 - dvC (stLen s.mem st) zl ml ≤ b2 →
      ReachesRet (LibW.program.link impl) ret0 S Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : S.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hk.jc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hk' := hk
  have epc := hk.pc; have e0 := hk.e0; have e1 := hk.e1; have e2 := hk.e2; have e4 := hk.e4; have e5 := hk.e5
  have e6 := hk.e6
  have s392 := hk.s392; have s264 := hk.s264; have s256 := hk.s256
  have esp := hk.jc.esp; have e28 := hk.jc.e28; have e29 := hk.jc.e29; have e18 := hk.jc.e18
  have s464 := hk.jc.sf.s464; have s520 := hk.jc.sf.s520; have s528 := hk.jc.sf.s528; have s536 := hk.jc.sf.s536
  have hB := hk.bb
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  obtain ⟨brr, brc⟩ := hB.br.lt64
  have bzl := hB.bz.2.1
  have bzzl := hB.lzz
  have brl := hB.lr
  have bst : st < 2 ^ 64 := by have := hP.stk0.2.2.2.1; omega
  obtain ⟨-, -, -, -, -, -, -, hmp, hmc, -⟩ :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hml0 := hP.2.2.2.2.2.1
  clear hB hk
  janus_run [hmacc] until [1806848]
  refine callL3 hap hns hnf hdv hkS haS hP hM hk' hcost KT _ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  case hF => simp only [wsL3]; janus_frame
  case hrg => simp only [Memory.regions_writeLE]
  all_goals (first | (janus_simp <;> omega) | (janus_simp; simp only [s392, s264, s256, s464, s520, s528, s536]))

end

end FvModexp.Arm64.ExpSlow
