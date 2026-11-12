import FvModexp.Proofs.Arm64.Exp.P2W2BJ

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): loop body segment B2 — `J2` → second `sqr` → `J3` (agent infra)

From the first `trunc`'s return `1796308`: `440/232/120 := Z1` (the new `zz` after the swap), `R3 := stk`,
`R4..R6 := Z1`, `R0..R2 := z` (slots `280/112/224`), `CALL nat.sqr` (return `1796352`; nat.go:1237-1239).
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
theorem callB2 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ K) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {i c yi Z : Nat} {u : Bool}
    (K3 : KJ impl ret0 Q (J3 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 pA lA cA p1 l1 c1 : Nat}
    (h : J2 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S0 M0 L1 b1 pA lA cA
      p1 l1 c1)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1815584) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + 440, sp + 440 + 8), (sp + 232, sp + 232 + 8), (sp + 120, sp + 120 + 8)])
    (hrg : T.mem.regions = M0.regions)
    (r440 : T.mem.readLE (sp + 440) 8 = p1) (r232 : T.mem.readLE (sp + 232) 8 = l1)
    (r120 : T.mem.readLE (sp + 120) 8 = c1) (h30 : T.regs 30 = BitVec.ofNat 64 (1795088 + 4 * 316))
    (h0 : T.regs 0 = BitVec.ofNat 64 pA) (h1 : T.regs 1 = BitVec.ofNat 64 lA) (h2 : T.regs 2 = BitVec.ofNat 64 cA)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 p1) (h5 : T.regs 5 = BitVec.ofNat 64 l1)
    (h6 : T.regs 6 = BitVec.ofNat 64 c1) :
    ReachesRet (LibExp.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hjc.bf hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [SW] <;> omega)
  have rk : ∀ a, (a + 8 ≤ sp + 120 ∨ (sp + 128 ≤ a ∧ a + 8 ≤ sp + 232) ∨ (sp + 240 ≤ a ∧ a + 8 ≤ sp + 440) ∨
      sp + 448 ≤ a) → T.mem.readLE a 8 = M0.readLE a 8 := fun a ha =>
    hF.readLE a 8 (outside_of_forall fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> omega)
  have hl1 := h.l1b
  have hlx0 : 0 < l1 := len_pos h.n1.2.1 h.n1.2.2.2
  have hc1 : 0 < c1 := by have := h.n1.1; omega
  obtain ⟨hA, -⟩ := hkeep u pA cA h.ca h.ca0
  obtain ⟨hZ1, hZ1k⟩ := hkeep (!u) p1 c1 h.r1 hc1
  have hZn : NV T.mem p1 l1 c1 (Z1 lm Z) := NV.keep h.n1 hZ1k
  have hmono := hsm (ℓL (stLen s.mem st) lm) l1 (W lm) hl1
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : sqC (ℓL (stLen s.mem st) lm) l1 ≤ b1 := by simp only [bodyB, SQ, ML] at hb hmono; omega
  refine sqrB hap hns hnf hsq hkS haS hP hB (v := u) hA h.ca0 h.lac hZ1 hZn hl1 hcst (by decide) T hpc hsp h28 rfl h30
    h0 h1 h2 h3 h4 h5 h6 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres hnv hl' hx hxn hbud
  have hc32 := hjc.hc
  exact K3 s' s'.mem L2 b2 p1 l1 c1 p' l' c'
    { jc := ⟨hsp'.trans hsp, h28'.trans h28, h29'.trans h29, h18'.trans h18, rfl, hB',
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s200),
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s208),
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s240),
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s160), hjc.hi, hjc.hyi,
        hjc.hc, hjc.hu, hjc.hfv, hcb⟩
      epc := hpc', e0 := e0, e1 := e1, e2 := e2, r2 := hres, n2 := hnv, l2b := hl', r1 := hx, n1 := hxn,
      l1b := hl1, s440 := (hslot _ _ (by omega) (by omega)).trans r440,
      s232 := (hslot _ _ (by omega) (by omega)).trans r232, s120 := (hslot _ _ (by omega) (by omega)).trans r120,
      hb := by simp only [bodyB, SQ, ML] at hb hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B2** -/
theorem segB2 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ K) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {i c yi Z : Nat} {u : Bool}
    (K3 : KJ impl ret0 Q (J3 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u)) :
    KJ impl ret0 Q (J2 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u) := by
  intro S M L1 b1 pA lA cA p1 l1 c1 h
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [h.jc.bf.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have r496 : M.readLE (sp + 496) 8 = st := h.jc.bf.esl.2.2.2.2.2.2.2.2.1
  have hst48 := h.jc.bf.wc.sok.2.2.2.1
  have hl1 := h.n1.1
  have hc1 : 0 < c1 := by have := len_pos h.n1.2.1 h.n1.2.2.2; omega
  have hf := BC.facts hP h.jc.bf h.r1 hc1
  have h140 := hf.1
  have h148 := (hf.2.1 hc1).2.2.2
  have hfA := BC.facts hP h.jc.bf h.ca h.ca0
  have hA40 := hfA.1
  have hA48 := (hfA.2.1 h.ca0).2.2.2
  have hlac := h.lac
  have r280 := h.s280
  have r112 := h.s112
  have r224 := h.s224
  have h' := h
  obtain ⟨⟨esp, e28, e29, e18, em, -⟩, epc, e0, e1, e2, -⟩ := h
  subst em
  janus_run [hmacc, r496, r280, r112, r224] until [1815584]
  refine callB2 hap hns hnf hsq hkS haS hsm hP K3 h' _ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case hF => janus_frame
  case hrg => simp only [Memory.regions_writeLE]
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W2
