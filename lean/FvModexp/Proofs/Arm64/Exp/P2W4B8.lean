import FvModexp.Proofs.Arm64.Exp.P2W4BJ
import FvModexp.Proofs.Arm64.Exp.P2W4Cp4

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): loop body segment B8 — `J8` → `mul` by `powers[yi >> 60]` → `J9` (agent infra)

From the fourth `trunc`'s return `0x1b6130`: `280/112/216 := Z4` (the new `zz` after the swap), `d = yi >> 60`
(slot 160), the header `powers[d]` (`sp + 320 + 24 d`), `R3 := stk`, `R4..R6 := Z4`, `R0..R2 := Z3` (slots
`728/232/120`), `R7..R9 := powers[d]`, `CALL nat.mul` (return `0x1b6188`; nat.go:1100-1102).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.EvenHyp

theorem d24 (yi : Nat) (hyi : yi < 2 ^ 64) :
    (BitVec.ofNat 64 yi >>> 60 <<< 3) + ((BitVec.ofNat 64 yi >>> 60 <<< 3) <<< 1) = BitVec.ofNat 64 (24 * dOf yi) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, dOf]
  omega

theorem rot60 (yi : Nat) (hyi : yi < 2 ^ 64) : ((BitVec.ofNat 64 yi).rotateRight 60).toNat % 16 = dOf yi := by
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hyi]
  have e : yi <<< (64 - 60 % 64) % 2 ^ 64 = (yi % 2 ^ 60) <<< 4 := by
    simp only [Nat.shiftLeft_eq, show 64 - 60 % 64 = 4 from rfl]; omega
  rw [e, show 60 % 64 = 60 from rfl, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (by rw [Nat.shiftRight_eq_div_pow]; omega)]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, dOf]; omega

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem callB8 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ K) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hX : natVal s.mem xp xl % 2 = 1)
    {i c yi Z : Nat} {u : Bool}
    (K9 : KJ impl ret0 Q (J9 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 po lo co pr lr cr : Nat}
    (h : J8 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S0 M0 L1 b1 po lo co
      pr lr cr)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1814128) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + 280, sp + 280 + 8), (sp + 112, sp + 112 + 8), (sp + 216, sp + 216 + 8)])
    (hrg : T.mem.regions = M0.regions)
    (r280 : T.mem.readLE (sp + 280) 8 = pr) (r112 : T.mem.readLE (sp + 112) 8 = lr)
    (r216 : T.mem.readLE (sp + 216) 8 = cr) (h30 : T.regs 30 = BitVec.ofNat 64 (1792928 + 4 * 378))
    (h0 : T.regs 0 = BitVec.ofNat 64 po) (h1 : T.regs 1 = BitVec.ofNat 64 lo) (h2 : T.regs 2 = BitVec.ofNat 64 co)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 pr) (h5 : T.regs 5 = BitVec.ofNat 64 lr)
    (h6 : T.regs 6 = BitVec.ofNat 64 cr) (h7 : T.regs 7 = BitVec.ofNat 64 (bp + 8 * (dOf yi * W lm)))
    (h8 : T.regs 8 = BitVec.ofNat 64 (M0.readLE (sp + 320 + 24 * dOf yi + 8) 8))
    (h9 : T.regs 9 = BitVec.ofNat 64 (W lm)) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hjc.bf hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [SW] <;> omega)
  have rk : ∀ a, (a + 8 ≤ sp + 112 ∨ (sp + 120 ≤ a ∧ a + 8 ≤ sp + 216) ∨ (sp + 224 ≤ a ∧ a + 8 ≤ sp + 280) ∨
      sp + 288 ≤ a) → T.mem.readLE a 8 = M0.readLE a 8 := fun a ha =>
    hF.readLE a 8 (outside_of_forall fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> omega)
  have hyi := hjc.hyi
  have hj : dOf yi < 16 := by simp only [dOf]; omega
  have hlr := h.lrb
  have hlx0 : 0 < lr := len_pos h.nr.2.1 h.nr.2.2.2
  have hcr : 0 < cr := by have := h.nr.1; omega
  have hlo := h.no.1
  have hco : 0 < co := by have := len_pos h.no.2.1 h.no.2.2.2; omega
  obtain ⟨hZ1, -⟩ := hkeep (!u) po co h.ro hco
  obtain ⟨hZ2, hZ2k⟩ := hkeep u pr cr h.rr hcr
  have hZn : NV T.mem pr lr cr (Z4 lm Z) := NV.keep h.nr hZ2k
  have hly : T.mem.readLE (sp + 320 + 24 * dOf yi + 8) 8 = M0.readLE (sp + 320 + 24 * dOf yi + 8) 8 :=
    hrd _ _ (by omega)
  have hlyW : M0.readLE (sp + 320 + 24 * dOf yi + 8) 8 ≤ W lm := (hjc.bf.tz.pw (dOf yi) hj).2.2.1
  have hmono := hmm (lvlL (stLen s.mem st) lm) lr (W lm) _ (W lm) hlr hlyW
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : mlC (lvlL (stLen s.mem st) lm) lr (M0.readLE (sp + 320 + 24 * dOf yi + 8) 8) ≤ b1 := by
    simp only [bodyB, ML] at hb hmono; omega
  have hPo := p2Pow_odd lm (natVal s.mem xp xl) (dOf yi) (by have := hP.2.2.2.2.2.1; omega) hX
  refine mulB hap hns hnf hmu hkM haM hP hB (v := !u) hZ1 hco hlo (by rw [Bool.not_not]; exact hZ2) hZn hlr hj hly
    hPo hcst (by decide) T hpc hsp h28 rfl h30 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres hnv hl' hx hxn hbud
  rw [Bool.not_not] at hx
  exact K9 s' s'.mem L2 b2 pr lr cr p' l' c'
    { jc := ⟨hsp'.trans hsp, h28'.trans h28, h29'.trans h29, h18'.trans h18, rfl, hB',
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s200),
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s208),
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s240),
        (hslot _ _ (by omega) (by omega)).trans ((rk _ (by omega)).trans hjc.s160), hjc.hi, hjc.hyi,
        hjc.hc, hjc.hu, hjc.hfv, hcb⟩
      epc := hpc', e0 := e0, e1 := e1, e2 := e2, rr := hres, nr := hnv, lrb := hl', ro := hx, no := hxn,
      lob := hlr, so1 := (hslot _ _ (by omega) (by omega)).trans r280,
      so2 := (hslot _ _ (by omega) (by omega)).trans r112, so3 := (hslot _ _ (by omega) (by omega)).trans r216,
      hb := by simp only [bodyB, ML] at hb hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B8** -/
theorem segB8 (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ K) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hX : natVal s.mem xp xl % 2 = 1)
    {i c yi Z : Nat} {u : Bool}
    (K9 : KJ impl ret0 Q (J9 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u)) :
    KJ impl ret0 Q (J8 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u) := by
  intro S M L1 b1 po lo co pr lr cr h
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 848) true = true := by
    rw [h.jc.bf.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have r784 : M.readLE (sp + 784) 8 = st := h.jc.bf.esl.2.2.2.2.2.2.2.2.1
  have hst48 := h.jc.bf.wc.sok.2.2.2.1
  have hyi := h.jc.hyi
  have hj : dOf yi < 16 := by simp only [dOf]; omega
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
  obtain ⟨t0, t2, t1, -, -⟩ := h.jc.bf.tz.pw (dOf yi) hj
  have hbs := h.jc.bf.tz.bscr
  have hb48 := hbs.b48
  have hjW : (dOf yi + 1) * W lm ≤ P2Pre.NB 16 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : dOf yi * W lm + W lm ≤ P2Pre.NB 16 lm := by rw [← Nat.succ_mul]; exact hjW
  have h2l := h.nr.1
  have hcr : 0 < cr := by have := len_pos h.nr.2.1 h.nr.2.2.2; omega
  have hf := BC.facts hP h.jc.bf h.rr hcr
  have h240 := hf.1
  have h248 := (hf.2.1 hcr).2.2.2
  have hlo := h.no.1
  have hco : 0 < co := by have := len_pos h.no.2.1 h.no.2.2.2; omega
  have hf1 := BC.facts hP h.jc.bf h.ro hco
  have h140 := hf1.1
  have h148 := (hf1.2.1 hco).2.2.2
  have r728 := h.so1
  have r232 := h.so2
  have r120 := h.so3
  have r160 := h.jc.s160
  have hd := d24 yi hyi
  have hrot := rot60 yi hyi
  have a1 : sp + 320 + (8 * dOf yi + 2 * (8 * dOf yi)) = sp + 320 + 24 * dOf yi := by omega
  have a2 : 8 * dOf yi + 2 * (8 * dOf yi) + (sp + 320) + 8 = sp + 320 + 24 * dOf yi + 8 := by omega
  have a3 : 8 * dOf yi + 2 * (8 * dOf yi) + (sp + 320) + 16 = sp + 320 + 24 * dOf yi + 16 := by omega
  have h' := h
  obtain ⟨⟨esp, e28, e29, e18, em, -⟩, epc, e0, e1, e2, -⟩ := h
  subst em
  janus_run [hmacc, r784, r728, r232, r120, r160, hd, t0, t1, t2] until [1814128]
  refine callB8 hap hns hnf hmu hkM haM hmm hP hX K9 h' _ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case hF => janus_frame
  case hrg => simp only [Memory.regions_writeLE]
  all_goals (janus_simp <;> (try simp only [hrot, a1, a2, a3, t0, t2]) <;> omega)

end

end FvModexp.Arm64.P2W4
