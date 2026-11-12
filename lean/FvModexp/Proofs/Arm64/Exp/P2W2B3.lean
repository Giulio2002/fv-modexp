import FvModexp.Proofs.Arm64.Exp.P2W2BJ

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): loop body segment B3 — `J3` → `z = z.trunc(z, logM)` → `J4` (agent infra)

From the return `1796352`: `R3..R5 := R0..R2`, `R6 := logM` (slot 552), `CALL nat.trunc` (return
`1796372`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem callB3 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (K4 : KJ impl ret0 Q (J4 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u))
    {S0 : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 p2 l2 c2 : Nat}
    (h : J3 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S0 M L1 b1 p1 l1 c1 p2 l2 c2)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1786000) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = M)
    (h30 : T.regs 30 = BitVec.ofNat 64 (1795088 + 4 * 321))
    (h0 : T.regs 0 = BitVec.ofNat 64 p2) (h1 : T.regs 1 = BitVec.ofNat 64 l2) (h2 : T.regs 2 = BitVec.ofNat 64 c2)
    (h3 : T.regs 3 = BitVec.ofNat 64 p2) (h4 : T.regs 4 = BitVec.ofNat 64 l2) (h5 : T.regs 5 = BitVec.ofNat 64 c2)
    (h6 : T.regs 6 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hB := h.jc.bf
  have hb := h.hb
  have hcb := h.jc.hcb
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
  have hl1 := h.l2b
  have hlx0 : 0 < l2 := len_pos h.n2.2.1 h.n2.2.2.2
  have hc1 : 0 < c2 := by have := h.n2.1; omega
  refine trB hap hns hnf htr hkT haT hP hB h.r2 h.n2 (by omega) (by simp only [bodyB] at hb; omega) (by decide) T hpc
    hsp h28 hm h30 h0 h1 h2 h3 h4 h5 h6 ?_
  intro s' L2 b2 l' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres hnv hl' hkeep hbud
  obtain ⟨hA, hAk⟩ := hkeep (!u) p1 c1 h.r1 (by have := len_pos h.n1.2.1 h.n1.2.2.2; have := h.n1.1; omega)
    (bc_apart hP hB h.r2 h.r1 hc1 (by have := len_pos h.n1.2.1 h.n1.2.2.2; have := h.n1.1; omega)).symm
  have hjc := h.jc
  exact K4 s' s'.mem L2 b2 p1 l1 c1 p2 l' c2
    { jc := hjc.call (hsp'.trans (hsp.trans hjc.esp.symm)) (h28'.trans (h28.trans hjc.e28.symm))
        (h29'.trans (h29.trans hjc.e29.symm)) (h18'.trans (h18.trans hjc.e18.symm)) rfl hB'
        hslot,
      epc := hpc', e0 := e0, e1 := e1, e2 := e2, r2 := hres, n2 := hnv, l2b := hl', r1 := hA,
      n1 := NV.keep h.n1 hAk, l1b := h.l1b, s440 := (hslot _ _ (by omega) (by omega)).trans h.s440,
      s232 := (hslot _ _ (by omega) (by omega)).trans h.s232, s120 := (hslot _ _ (by omega) (by omega)).trans h.s120,
      hb := by simp only [bodyB] at hb ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B3** -/
theorem segB3 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (K4 : KJ impl ret0 Q (J4 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u)) :
    KJ impl ret0 Q (J3 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u) := by
  intro S M L1 b1 p1 l1 c1 p2 l2 c2 h
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [h.jc.bf.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have r552 : M.readLE (sp + 552) 8 = lm := h.jc.bf.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hl1 := h.n2.1
  have hc1 : 0 < c2 := by have := len_pos h.n2.2.1 h.n2.2.2.2; omega
  have hf := BC.facts hP h.jc.bf h.r2 hc1
  have h140 := hf.1
  have h148 := (hf.2.1 hc1).2.2.2
  have h' := h
  obtain ⟨⟨esp, e28, e29, e18, em, -⟩, epc, e0, e1, e2, -⟩ := h
  subst em
  janus_run [hmacc, r552] until [1786000]
  refine callB3 hap hns hnf htr hkT haT hP K4 h' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W2
