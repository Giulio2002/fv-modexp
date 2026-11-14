import FvModexp.Proofs.Amd64.Exp.P2W2BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): loop body segment B2 — `J2` → second `sqr` → `J3` (agent divmc s73; amd64
twin of agent infra's `Arm64.P2W2B2`)

From the `trunc` return fn+0x68d: the stores `0x1b8/0xd8/0x70 := Z1 = (AX, BX, CX)`, `DI := [0x208] = stk`,
`SI, R8, R9 := Z1`, `AX, BX, CX := [0x118], [0x68], [0xe0]` (= `z`), `z = z.sqr(stk, zz)` (nat.go:1239; `CALL` at
fn+0x6c8, return fn+0x6cd).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the second `sqr` call from the stores' memory (`T` = the callee entry state) -/
theorem callB2 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {i c yi Z : Nat} {u : Bool}
    (K3 : KJ impl ret0 Q (J3 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 pA lA cA p1 l1 c1 : Nat}
    (h : J2 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S0 M0 L1 b1 pA lA cA p1 l1
      c1)
    {M1 : Memory} (hF : MemFrame M0 M1 [(sp + 440, sp + 440 + 8), (sp + 216, sp + 216 + 8), (sp + 112, sp + 112 + 8)])
    (hrg : M1.regions = M0.regions)
    (r1b8 : M1.readLE (sp + 440) 8 = p1) (rd8 : M1.readLE (sp + 216) 8 = l1) (r70 : M1.readLE (sp + 112) 8 = c1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6229984) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M1.writeLE (sp - 8) 8 6202605)
    (h0 : T.regs 0 = BitVec.ofNat 64 pA) (h3 : T.regs 3 = BitVec.ofNat 64 lA) (h1 : T.regs 1 = BitVec.ofNat 64 cA)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 p1) (h8 : T.regs 8 = BitVec.ofNat 64 l1)
    (h9 : T.regs 9 = BitVec.ofNat 64 c1) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hjc.bf hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hB 6202605
  have hlA := len_pos h.na.2.1 h.na.2.2.2
  have hcA : 0 < cA := by have := h.na.1; omega
  have hl1 := len_pos h.n1.2.1 h.n1.2.2.2
  have hc1 : 0 < c1 := by have := h.n1.1; omega
  obtain ⟨hA, -⟩ := hkeep u pA cA h.ca hcA
  obtain ⟨hA2, -⟩ := hkeep2 u pA cA hA hcA
  obtain ⟨h11, h1k⟩ := hkeep (!u) p1 c1 h.r1 hc1
  obtain ⟨h12, h1k2⟩ := hkeep2 (!u) p1 c1 h11 hc1
  have h1n : NV (M1.writeLE (sp - 8) 8 6202605) p1 l1 c1 (Z1 lm Z) :=
    NV.keep h.n1 fun a k a1 a2 => (h1k2 a k a1 a2).trans (h1k a k a1 a2)
  have hmono := sqrCQ_mono h.l1b
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : sqrCQ l1 ≤ b1 := by simp only [bodyB] at hb; omega
  have hra : (M1.writeLE (sp - 8) 8 6202605).readLE (sp - 8) 8 = 6200864 + 0x6cd :=
    Janus.Arm64.Memory.readLE_writeLE_self ..
  have hsl : ∀ a, (a = sp + 0xc0 ∨ a = sp + 0xc8 ∨ a = sp + 0xf0 ∨ a = sp + 0x98) →
      (M1.writeLE (sp - 8) 8 6202605).readLE a 8 = M0.readLE a 8 :=
    fun a ha => (hrd2 a 8 (by omega)).trans (hF.readLE a 8 (by
      rcases ha with rfl | rfl | rfl | rfl <;> simp only [outside_cons, outside_nil, and_true] <;> omega))
  rw [← hm] at hB2 hra h12 hA2 h1n hsl hrd2
  refine sqrB hap hns hnf hsq hkS hkS1 hP hadx hB2 (v := u) hA2 hcA h.na.1 h12 h1n h.l1b hcst (idx := 0x6cd)
    (by decide) T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hx hxn hbud
  have q : ∀ a, sp + 0x50 ≤ a → a + 8 ≤ sp + 0x230 → s'.mem.readLE a 8 = M1.readLE a 8 := fun a h1 h2 =>
    (hslot a 8 h1 h2).trans (hrd2 a 8 (by omega))
  have q0 : ∀ a, (a = sp + 0xc0 ∨ a = sp + 0xc8 ∨ a = sp + 0xf0 ∨ a = sp + 0x98) →
      s'.mem.readLE a 8 = M0.readLE a 8 := fun a ha => (hslot a 8 (by omega) (by omega)).trans (hsl a ha)
  exact K3 s' s'.mem L2 b2 p1 l1 c1 p' l' c'
    { jc := ⟨hsp', h14'.trans h14, h5'.trans h5, hfs', hx15', hdf', rfl, hB',
        (q0 _ (Or.inl rfl)).trans hjc.sc0, (q0 _ (Or.inr (Or.inl rfl))).trans hjc.sc8,
        (q0 _ (Or.inr (Or.inr (Or.inl rfl)))).trans hjc.sf0, (q0 _ (Or.inr (Or.inr (Or.inr rfl)))).trans hjc.s98,
        hjc.hi, hjc.hyi, hjc.hc, hjc.hu, hjc.hfv, hcb⟩
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, r2 := hres, n2 := hnv, l2b := hl', r1 := hx, n1 := hxn,
      l1b := h.l1b, s1b8 := (q _ (by omega) (by omega)).trans r1b8, sd8 := (q _ (by omega) (by omega)).trans rd8,
      s70 := (q _ (by omega) (by omega)).trans r70,
      hb := by simp only [bodyB] at hb hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B2** -/
theorem segB2 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {i c yi Z : Nat} {u : Bool}
    (K3 : KJ impl ret0 Q (J3 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u)) :
    KJ impl ret0 Q (J2 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) := by
  intro S M L1 b1 pA lA cA p1 l1 c1 h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x238 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have q208 : M.readLE (sp + 0x208) 8 = st := h.jc.bf.esl.2.2.2.2.2.2.2.2.1
  have hc1 : 0 < c1 := by have := len_pos h.n1.2.1 h.n1.2.2.2; have := h.n1.1; omega
  have h1f := BC.facts hP h.jc.bf h.r1 hc1
  have hc140 : c1 < 2 ^ 40 := h1f.1
  have hp1 : p1 + 8 * c1 ≤ 2 ^ 48 := (h1f.2.1 hc1).2.2.2
  have hl1c : l1 ≤ c1 := h.n1.1
  clear h1f
  have q118 := h.s118
  have q68 := h.s68
  have qe0 := h.se0
  have hH : HdM (J2 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1 pA lA cA p1
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
  janus64_run [q208, q118, q68, qe0, hwacc, hwaccF] until [6229984]
  refine callB2 hap hns hnf hsq hkS hkS1 hPH.h hadx K3 hH.h ?hF ?hrg ?r1 ?r2 ?r3 _ ?_ ?hsp ?_ ?_ ?hfs ?_ ?_ rfl ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  case hF => janus_frame
  case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case hfs => exact efs
  case hsp => janus64_simp; exact bv_sub8 (by omega) (by omega)
  case r1 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case r2 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case r3 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
  all_goals (janus64_simp; done)

end

end FvModexp.Amd64.P2W2
