import FvModexp.Proofs.Arm64.Exp.P2W4BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): loop body segment B0 — loop test → first `sqr` → `J1` (agent infra)

From `LT` with `c + 1` windows left: the test's stores `280 := z.ptr`, `112 := z.len`, `TBZ $63, k` (taken: `k = c ≥ 0`),
the body's stores `240 := k`, `224 := z.cap`, `160 := yi`, the argument moves and `zz = zz.sqr(stk, z)`
(nat.go:1223-1235; call `0x1b68bc`, return `1796288`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.EvenHyp

theorem bud_c1 (B X : Nat) (c i : Nat) : (c + 1 + 16 * i) * X = (c + 16 * i) * X + X := by
  rw [show c + 1 + 16 * i = (c + 16 * i) + 1 by omega, Nat.succ_mul]

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the first `sqr` call from the stores' memory (pure; `T` = the call state) -/
theorem callB0 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ K) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hcb : cst ≤ b) {i c yi Z : Nat} {u : Bool}
    (K1 : KJ impl ret0 Q (J1 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 pA lA cA pB lB cB : Nat}
    (h : KS R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV S0 M0 L1 b1 i (c + 1) yi Z pA lA
      cA pB lB cB u)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1815584) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + 112, sp + 112 + 8), (sp + 280, sp + 280 + 8), (sp + 224, sp + 224 + 8),
      (sp + 240, sp + 240 + 8), (sp + 160, sp + 160 + 8)]) (hrg : T.mem.regions = M0.regions)
    (r280 : T.mem.readLE (sp + 280) 8 = pA) (r112 : T.mem.readLE (sp + 112) 8 = lA)
    (r240 : T.mem.readLE (sp + 240) 8 = c) (r224 : T.mem.readLE (sp + 224) 8 = cA)
    (r160 : T.mem.readLE (sp + 160) 8 = yi) (h30 : T.regs 30 = BitVec.ofNat 64 (1792928 + 4 * 303))
    (h0 : T.regs 0 = BitVec.ofNat 64 pB) (h1 : T.regs 1 = BitVec.ofNat 64 lB) (h2 : T.regs 2 = BitVec.ofNat 64 cB)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 pA) (h5 : T.regs 5 = BitVec.ofNat 64 lA)
    (h6 : T.regs 6 = BitVec.ofNat 64 cA) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have li := h.li
  have hBF : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M0 L1 b1 zzp bp := ⟨li.wc, li.esl, li.tz⟩
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hBF hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [SW] <;> omega)
  have hlA := len_pos li.va li.zo
  have hcA : 0 < cA := by have := li.lac; omega
  obtain ⟨hA, hAk⟩ := hkeep u pA cA li.ca hcA
  obtain ⟨hBc, -⟩ := hkeep (!u) pB cB li.cb li.cb0
  have hAn : NV T.mem pA lA cA Z := NV.keep ⟨li.lac, li.va, li.na, li.zo⟩ hAk
  have hmono := hsm (lvlL (stLen s.mem st) lm) lA (W lm) li.la
  have hb := h.hb
  rw [bud_c1 0 _ c i] at hb
  have hcst : sqC (lvlL (stLen s.mem st) lm) lA ≤ b1 := by simp only [bc] at hb; omega
  refine sqrB hap hns hnf hsq hkS haS hP hB (v := !u) hBc li.cb0 li.lbc (by rw [Bool.not_not]; exact hA) hAn li.la
    hcst (by decide) T hpc hsp h28 rfl h30 h0 h1 h2 h3 h4 h5 h6 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres hnv hl' hx hxn hbud
  rw [Bool.not_not] at hx
  have hc32 := h.hc
  exact K1 s' s'.mem L2 b2 pA lA cA p' l' c'
    { jc := ⟨hsp'.trans hsp, h28'.trans h28, h29'.trans h29, h18'.trans h18, rfl, hB',
        (hslot _ _ (by omega) (by omega)).trans ((hrd _ _ (by omega)).trans li.s200),
        (hslot _ _ (by omega) (by omega)).trans ((hrd _ _ (by omega)).trans li.s208),
        (hslot _ _ (by omega) (by omega)).trans r240, (hslot _ _ (by omega) (by omega)).trans r160, h.hi, h.hyi,
        by omega, h.hu, h.hfv, hcb⟩
      epc := hpc', e0 := e0, e1 := e1, e2 := e2, rr := hres, nr := hnv, lrb := hl', ro := hx, no := hxn,
      lob := li.la, so1 := (hslot _ _ (by omega) (by omega)).trans r280,
      so2 := (hslot _ _ (by omega) (by omega)).trans r112, so3 := (hslot _ _ (by omega) (by omega)).trans r224,
      hb := by simp only [bc, bodyB, SQ, ML] at hb hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B0**: the body premise's first segment, from `KS` at the loop test with `c + 1` windows left -/
theorem segB0 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ K) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hcb : cst ≤ b) {i c yi Z : Nat} {u : Bool}
    (K1 : KJ impl ret0 Q (J1 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u))
    (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 pA lA cA pB lB cB : Nat)
    (h : KS R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV S M L1 b1 i (c + 1) yi Z pA lA
      cA pB lB cB u) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 848) true = true := by
    rw [h.li.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hc32 := h.hc
  have e7' : S.regs 7 = BitVec.ofNat 64 c := h.e7.trans (sub1c c (by omega))
  have hbit := bit63_c (c := c) (by omega)
  have hlA := len_pos h.li.va h.li.zo
  have hcA : 0 < cA := by have := h.li.lac; omega
  have hBF : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp := ⟨h.li.wc, h.li.esl, h.li.tz⟩
  have hAf := BC.facts hP hBF h.li.ca hcA
  have hA40 := hAf.1
  have hA48 := (hAf.2.1 hcA).2.2.2
  have hlac := h.li.lac
  have hyi := h.hyi
  have h' := h
  obtain ⟨epc, esp, e28, e29, e18, em, e3, e1, e14, e0, e15, e13, e8, -, e4, e9, e10, e11, e12, e2, -, -, -, -, -,
    -, -⟩ := h
  subst em
  janus_run [hbit, hmacc] until [1815584]
  refine callB0 hap hns hnf hsq hkS haS hsm hP hcb K1 h' _ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case hF => janus_frame
  case hrg => simp only [Memory.regions_writeLE]
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W4
