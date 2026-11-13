import FvModexp.Proofs.Arm64.ExpQ.SlowMuQ
import FvModexp.Proofs.Arm64.Exp.SlowL2

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowU2.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): lower-loop segment U2 — `KS2` → `if v & mask ≠ 0 { zz = zz.mul(stk, z, x) }` → `KD2`

At the `sqr` return (`fnE + 0x424`): `R3 := v` (slot 160), `TBNZ $63, R3`:
* bit 63 clear: `zz := (336, 120, 128)` in `(X6, X4, X5)`, `JMP` → `JD = fnE + 0x484` (`kdN`);
* bit 63 set: stores `416 := z.ptr`, `312 := z.len`, `304 := z.cap`, `CALL nat.mul(zz, stk, z, x)` (return
  `fnE + 0x474`, index 169), then `zz := (416, 312, 304)` in `(X6, X4, X5)`, `R3 := v` → `JD` (`callL2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpEven (MulHypG)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- bit 63 set: the `mul` call from the stores' memory (pure; `T` = the call state) -/
theorem callL2Q {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {mlC : Nat → Nat → Nat} {H : Nat} (hmu : MulHypGQ impl R ns stkS aboveS mlC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : SlowX R L xp xl xc) (hxl0 : 0 < xl)
    {ret0 : BitVec 64} {Q : State → Prop} {S0 : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KS2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S0 L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : mlC zl xl + stkR H S0.mem st ≤ b1)
    (KD : ∀ (S : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat),
      KD2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L2 b2 j w v p' l' c'
        (Zv * natVal s.mem xp xl) z zl zc' r rl rc q ql qc → b1 - (mlC zl xl + stkR H S0.mem st) + stkR H S.mem st ≤ b2 →
      ReachesRet (LibW.program.link impl) ret0 S Q)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1814128) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = BitVec.ofNat 64 (sp - 8)) (h18 : T.regs 18 = r18)
    (hF : MemFrame S0.mem T.mem (wsL2 sp)) (hrg : T.mem.regions = S0.mem.regions)
    (r376 : T.mem.readLE (sp + 376) 8 = z) (r224 : T.mem.readLE (sp + 224) 8 = zl)
    (r232 : T.mem.readLE (sp + 232) 8 = zc')
    (h30 : T.regs 30 = BitVec.ofNat 64 (1788352 + 4 * 285))
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h1 : T.regs 1 = BitVec.ofNat 64 zzl) (h2 : T.regs 2 = BitVec.ofNat 64 zzc)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 z) (h5 : T.regs 5 = BitVec.ofNat 64 zl)
    (h6 : T.regs 6 = BitVec.ofNat 64 zc') (h7 : T.regs 7 = BitVec.ofNat 64 xp) (h8 : T.regs 8 = BitVec.ofNat 64 xl)
    (h9 : T.regs 9 = BitVec.ofNat 64 xc) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T T.mem L1 b1 :=
    JC.frameW hP hk.jc (wsL2_in sp) hF hrg hsp h28 h29 h18
  have hB := BB.frameW hP (wsL2_in sp) hF hk.bb
  have hs13 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz := hk.zl256
  have hml := hP.2.2.2.2.2.2.1
  have hw63 := hk.w63
  have hrT : ∀ a, (a + 8 ≤ sp + 224 ∨ sp + 240 ≤ a ∧ a + 8 ≤ sp + 376 ∨ sp + 384 ≤ a) → T.mem.readLE a 8 = S0.mem.readLE a 8 :=
    fun a ha => hF.readLE _ _ (by simp only [wsL2, outside_cons, outside_nil, and_true]; omega)
  have eR := stkRW hP (wsL2_in sp) hF H
  refine mulSQ hap hns hnf hmu hkS haS hP hX hxl0 hj hB (by omega) (by omega) (lvl_mu hz (Nat.le_max_left xl ml) hH) (by rw [eR]; exact hcost)
    (idx := 285) (by decide) hpc h30
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 fun s' L2 b2 p' l' c' hpc' hj' hkp e0 e1 e2 hB' hl' hbud => ?_
  have hr : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 424 → s'.mem.readLE a 8 = T.mem.readLE a 8 :=
    fun a h1 h2 => hkp a 8 (Or.inr ⟨h1, by omega⟩)
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : s'.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hj'.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have q376 : s'.mem.readLE (sp + 376) 8 = z := (hr _ (by omega) (by omega)).trans r376
  have q224 : s'.mem.readLE (sp + 224) 8 = zl := (hr _ (by omega) (by omega)).trans r224
  have q232 : s'.mem.readLE (sp + 232) 8 = zc' := (hr _ (by omega) (by omega)).trans r232
  have q160 : s'.mem.readLE (sp + 160) 8 = v.toNat :=
    (hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s160)
  have hjs := hj'
  have esp := hjs.esp; have e28 := hjs.e28; have e29 := hjs.e29; have e18 := hjs.e18
  clear hjs
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  have bzl := hB.bz.2.1
  have hv := v.isLt
  janus_run [hmacc] until [1789508]
  refine KD _ L2 b2 p' l' c' (mkKD2 hP hj' hB' (by have := hk.zl256; omega) hk.jw hw63
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s216))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s392))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s264))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s256))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s400))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s280))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s272))
    ((hr _ (by omega) (by omega)).trans ((hrT _ (by omega)).trans hk.s200)) q160 _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_
    ?_) (by rw [eR] at hbud; exact hbud)
  all_goals (first | (janus_simp <;> omega) | (janus_simp; simp only [r376, r224, r232, hk.s160, BitVec.ofNat_toNat, BitVec.setWidth_eq]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **U2**: from `KS2` to `JD` (`KD2`), through `mul` when bit 63 of `v` is set -/
theorem segL2Q {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {mlC : Nat → Nat → Nat} {H : Nat} (hmu : MulHypGQ impl R ns stkS aboveS mlC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 120) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hX : SlowX R L xp xl xc) (hxl0 : 0 < xl)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KS2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : mlC zl xl + stkR H S.mem st ≤ b1)
    (KD : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 z' zl' zc' zz' zzl' zzc' : Nat),
      KD2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L2 b2 j w v z' zl' zc'
        (if v.getLsbD 63 = true then Zv * natVal s.mem xp xl else Zv) zz' zzl' zzc' r rl rc q ql qc →
      b1 - ((if v.getLsbD 63 = true then mlC zl xl else 0) + stkR H S.mem st) + stkR H S'.mem st ≤ b2 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : S.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hk.jc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hk' := hk
  have epc := hk.pc; have e0 := hk.e0; have e1 := hk.e1; have e2 := hk.e2
  have s384 := hk.s384; have s248 := hk.s248; have s240 := hk.s240; have s160 := hk.s160
  have esp := hk.jc.esp; have e28 := hk.jc.e28; have e29 := hk.jc.e29; have e18 := hk.jc.e18
  have s464 := hk.jc.sf.s464; have s472 := hk.jc.sf.s472; have s480 := hk.jc.sf.s480; have s488 := hk.jc.sf.s488
  have hB := hk.bb
  obtain ⟨bz, bzc⟩ := hB.bz.1.lt64
  obtain ⟨bzz, bzzc⟩ := hB.bzz.lt64
  have bzl := hB.bz.2.1
  have bzzl := hB.lzz
  have bst : st < 2 ^ 64 := by have := hP.stk0.2.2.2.1; omega
  have hxp := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxc := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hB hk
  have ev : BitVec.ofNat 64 v.toNat = v := BitVec.ofNat_toNat 64 v
  by_cases hd : v.getLsbD 63 = true
  · have h63 : (BitVec.ofNat 64 (S.mem.readLE (sp + 160) 8)).getLsbD 63 = true := by rw [s160, ev]; exact hd
    janus_run [h63, hmacc] until [1814128]
    refine callL2Q hap hns hnf hmu hkS haS hP hX hxl0 hk' hH hcost (fun S' L2 b2 p' l' c' hkd hb =>
      KD S' L2 b2 p' l' c' z zl zc' (by rw [if_pos hd]; exact hkd) (by rw [if_pos hd]; exact hb)) _ ?_ ?_ ?_ ?_ ?_
      ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case hF => simp only [wsL2]; janus_frame
    case hrg => simp only [Memory.regions_writeLE]
    all_goals (first | (janus_simp <;> omega) | (janus_simp; simp only [s384, s248, s240, s160, s464, s472, s480, s488, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
  · have h63 : (BitVec.ofNat 64 (S.mem.readLE (sp + 160) 8)).getLsbD 63 = false := by
      rw [s160, ev]; simpa using hd
    janus_run [h63, hmacc] until [1789508]
    refine KD _ L1 b1 z zl zc' zz zzl zzc ?_ (by rw [if_neg hd]; show b1 - (0 + stkR H S.mem st) + stkR H S.mem st ≤ b1; omega)
    rw [if_neg hd]
    refine mkKD2 hP hk'.jc hk'.bb (by have := hk'.zl256; omega) hk'.jw hk'.w63 hk'.s216 hk'.s392 hk'.s264 hk'.s256
      hk'.s400 hk'.s280 hk'.s272 hk'.s200 hk'.s160 _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (first | (janus_simp <;> omega) | (janus_simp; simp only [s384, s248, s240, s160, s464, s472, s480, s488, BitVec.ofNat_toNat, BitVec.setWidth_eq]))

end

end FvModexp.Arm64.Q.ExpSlow
