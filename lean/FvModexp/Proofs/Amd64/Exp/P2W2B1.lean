import FvModexp.Proofs.Amd64.Exp.P2W2BJ
import FvModexp.Proofs.Amd64.Exp.P2W2Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): loop body segment B1 — `J1` → first `trunc` → `J2` (agent divmc s73; amd64
twin of agent infra's `Arm64.P2W2B1`)

From the `sqr` return fn+0x677: `DI, SI, R8 := AX, BX, CX`, `R9 := [0x228] = logM`, `zz = zz.trunc(zz, logM)`
(nat.go:1237; `CALL` at fn+0x688, return fn+0x68d).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the first `trunc` call (`T` = the callee entry state) -/
theorem callB1 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (K2 : KJ impl ret0 Q (J2 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 pA lA cA p1 l1 c1 : Nat}
    (h : J1 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S0 M0 L1 b1 pA lA cA p1 l1
      c1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6188320) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M0.writeLE (sp - 8) 8 6202541)
    (h0 : T.regs 0 = BitVec.ofNat 64 p1) (h3 : T.regs 3 = BitVec.ofNat 64 l1) (h1 : T.regs 1 = BitVec.ofNat 64 c1)
    (h7 : T.regs 7 = BitVec.ofNat 64 p1) (h6 : T.regs 6 = BitVec.ofNat 64 l1) (h8 : T.regs 8 = BitVec.ofNat 64 c1)
    (h9 : T.regs 9 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hjc.bf 6202541
  have hlA := len_pos h.na.2.1 h.na.2.2.2
  have hcA : 0 < cA := by have := h.na.1; omega
  have hc1 : 0 < c1 := by have := len_pos h.n1.2.1 h.n1.2.2.2; have := h.n1.1; omega
  obtain ⟨hA2, hAk2⟩ := hkeep2 u pA cA h.ca hcA
  obtain ⟨h12, h1k2⟩ := hkeep2 (!u) p1 c1 h.r1 hc1
  have hAn : NV (M0.writeLE (sp - 8) 8 6202541) pA lA cA Z := NV.keep h.na hAk2
  have h1n : NV (M0.writeLE (sp - 8) 8 6202541) p1 l1 c1 (Z * Z) := NV.keep h.n1 h1k2
  have hap1 := bc_apart hjc.bf h.ca h.r1 hcA hc1
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : P2Pre.tC lm ≤ b1 := by simp only [bodyB] at hb; omega
  have hra : (M0.writeLE (sp - 8) 8 6202541).readLE (sp - 8) 8 = 6200864 + 0x68d :=
    Janus.Arm64.Memory.readLE_writeLE_self ..
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  rw [← hm] at hB2 hra h12 hA2 hAn h1n hrd2
  refine trB hap hns hnf htr hkT haT hP hB2 (v := !u) h12 h1n (by have := h.l1b; omega) hcst (idx := 0x68d)
    (by decide) T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 l' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hk hbud
  obtain ⟨hA', hAk'⟩ := hk u pA cA hA2 hcA hap1
  have q : ∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x230 → s'.mem.readLE a k = M0.readLE a k := fun a k h1 h2 =>
    (hslot a k h1 h2).trans (hrd2 a k (by omega))
  exact K2 s' s'.mem L2 b2 pA lA cA p1 l' c1
    { jc := hjc.call (hsp'.trans hjc.esp.symm) ((h14'.trans h14).trans hjc.e14.symm)
        ((h5'.trans h5).trans hjc.e5.symm) hfs' hx15' hdf' rfl hB' q
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, r1 := hres, n1 := hnv, l1b := hl', ca := hA',
      na := NV.keep hAn hAk', la := h.la, s118 := (q _ _ (by omega) (by omega)).trans h.s118,
      s68 := (q _ _ (by omega) (by omega)).trans h.s68, se0 := (q _ _ (by omega) (by omega)).trans h.se0,
      hb := by simp only [bodyB] at hb hbud ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B1** -/
theorem segB1 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (K2 : KJ impl ret0 Q (J2 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u)) :
    KJ impl ret0 Q (J1 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) := by
  intro S M L1 b1 pA lA cA p1 l1 c1 h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x238 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have q228 : M.readLE (sp + 0x228) 8 = lm := h.jc.bf.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hH : HdM (J1 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1 pA lA cA p1
    l1 c1) := ⟨h⟩
  have epc := h.epc
  have esp := h.jc.esp
  have e14 := h.jc.e14
  have e5 := h.jc.e5
  have efs := h.jc.efs
  have ex := h.jc.ex
  have edf := h.jc.edf
  have e0 := h.e0
  have e3 := h.e3
  have e1 := h.e1
  have em := h.jc.em
  clear h hce
  have hPH : HdM (EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) := ⟨hP⟩
  clear hP
  subst em
  refine SegProg.lift P2W2Seg.codeIn (r := BitVec.ofNat 64 6188320) ?_
  janus64_run [q228, hwacc, hwaccF] until [6188320]
  refine callB1 hap hns hnf htr hkT haT hPH.h K2 hH.h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | exact efs
    | (janus64_simp; done)
    | (janus64_simp; exact bv_sub8 (by omega) (by omega))

end

end FvModexp.Amd64.P2W2
