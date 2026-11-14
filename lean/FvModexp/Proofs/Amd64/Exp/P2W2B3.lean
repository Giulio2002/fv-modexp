import FvModexp.Proofs.Amd64.Exp.P2W2BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): loop body segment B3 — `J3` → second `trunc` → `J4` (agent divmc s73; amd64
twin of agent infra's `Arm64.P2W2B3`)

From the `sqr` return fn+0x6cd: `DI, SI, R8 := AX, BX, CX`, `R9 := [0x228] = logM`, `zz = zz.trunc(zz, logM)`
(nat.go:1241; `CALL` at fn+0x6e0, return fn+0x6e5).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the second `trunc` call (`T` = the callee entry state) -/
theorem callB3 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (K4 : KJ impl ret0 Q (J4 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 p2 l2 c2 : Nat}
    (h : J3 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S0 M0 L1 b1 p1 l1 c1 p2 l2
      c2)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6188320) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M0.writeLE (sp - 8) 8 6202629)
    (h0 : T.regs 0 = BitVec.ofNat 64 p2) (h3 : T.regs 3 = BitVec.ofNat 64 l2) (h1 : T.regs 1 = BitVec.ofNat 64 c2)
    (h7 : T.regs 7 = BitVec.ofNat 64 p2) (h6 : T.regs 6 = BitVec.ofNat 64 l2) (h8 : T.regs 8 = BitVec.ofNat 64 c2)
    (h9 : T.regs 9 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hjc.bf 6202629
  have hlA := len_pos h.n1.2.1 h.n1.2.2.2
  have hc1 : 0 < c1 := by have := h.n1.1; omega
  have hc2 : 0 < c2 := by have := len_pos h.n2.2.1 h.n2.2.2.2; have := h.n2.1; omega
  obtain ⟨hA2, hAk2⟩ := hkeep2 (!u) p1 c1 h.r1 hc1
  obtain ⟨h12, h1k2⟩ := hkeep2 u p2 c2 h.r2 hc2
  have hAn : NV (M0.writeLE (sp - 8) 8 6202629) p1 l1 c1 (Z1 lm Z) := NV.keep h.n1 hAk2
  have h1n : NV (M0.writeLE (sp - 8) 8 6202629) p2 l2 c2 (Z1 lm Z * Z1 lm Z) := NV.keep h.n2 h1k2
  have hap1 := (bc_apart hjc.bf h.r2 h.r1 hc2 hc1).symm
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : P2Pre.tC lm ≤ b1 := by simp only [bodyB] at hb; omega
  have hra : (M0.writeLE (sp - 8) 8 6202629).readLE (sp - 8) 8 = 6200864 + 0x6e5 :=
    Janus.Arm64.Memory.readLE_writeLE_self ..
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  rw [← hm] at hB2 hra h12 hA2 hAn h1n hrd2
  refine trB hap hns hnf htr hkT haT hP hB2 (v := u) h12 h1n (by have := h.l2b; omega) hcst (idx := 0x6e5)
    (by decide) T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 l' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hk hbud
  obtain ⟨hA', hAk'⟩ := hk (!u) p1 c1 hA2 hc1 hap1
  have q : ∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x230 → s'.mem.readLE a k = M0.readLE a k := fun a k h1 h2 =>
    (hslot a k h1 h2).trans (hrd2 a k (by omega))
  exact K4 s' s'.mem L2 b2 p1 l1 c1 p2 l' c2
    { jc := hjc.call (hsp'.trans hjc.esp.symm) ((h14'.trans h14).trans hjc.e14.symm)
        ((h5'.trans h5).trans hjc.e5.symm) hfs' hx15' hdf' rfl hB' q
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, r2 := hres, n2 := hnv, l2b := hl', r1 := hA',
      n1 := NV.keep hAn hAk', l1b := h.l1b, s1b8 := (q _ _ (by omega) (by omega)).trans h.s1b8,
      sd8 := (q _ _ (by omega) (by omega)).trans h.sd8, s70 := (q _ _ (by omega) (by omega)).trans h.s70,
      hb := by simp only [bodyB] at hb hbud ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B3** -/
theorem segB3 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (K4 : KJ impl ret0 Q (J4 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u)) :
    KJ impl ret0 Q (J3 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) := by
  intro S M L1 b1 p1 l1 c1 p2 l2 c2 h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x238 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have q228 : M.readLE (sp + 0x228) 8 = lm := h.jc.bf.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hH : HdM (J3 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1 p1 l1 c1 p2
    l2 c2) := ⟨h⟩
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
  janus64_run [q228, hwacc, hwaccF] until [6188320]
  refine callB3 hap hns hnf htr hkT haT hPH.h K4 hH.h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | exact efs
    | (janus64_simp; done)
    | (janus64_simp; exact bv_sub8 (by omega) (by omega))

end

end FvModexp.Amd64.P2W2
