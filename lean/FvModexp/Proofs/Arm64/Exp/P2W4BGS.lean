import FvModexp.Proofs.Arm64.Exp.P2W4BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the body's generic `sqr` step (agent infra)

`callS`: at the `nat.sqr` entry (`zz = zz.sqr(stk, z)`, return `fn + 4 idx`) from a join point
`JX pcT v w Vr lrb Vo o1 o2 o3 rem` (a `trunc` just returned `z = (pr, lr, cr)`; the destination `zz` is the other
buffer `(po, lo, co)`), after the spills of `z` to `n1/n2/n3` (`728/232/120` or `280/112/216`): the continuation
gets `JX (fn + 4 idx) w v (Vr²) 2w Vr n1 n2 n3 rem'` for any `rem' + sqr ≤ rem`. Shared by the sqr segments
`B2/B4/B6` (window-4 generalisation of the window-2 `callB2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)
open FvModexp.Arm64.EvenHyp

/-- the two spill triples of the body -/
@[reducible] def NS (n1 n2 n3 : Nat) : Prop := (n1 = 728 ∧ n2 = 232 ∧ n3 = 120) ∨ (n1 = 280 ∧ n2 = 112 ∧ n3 = 216)

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem callS (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ K) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {i c yi Z : Nat} {u : Bool}
    {pcT : Nat} {v w : Bool} {Vr lrb Vo o1 o2 o3 rem rem' idx n1 n2 n3 : Nat} (hvw : v = !w) (hlrb : lrb ≤ W lm)
    (hn : NS n1 n2 n3) (hrem : rem' + SQ s st lm sqC ≤ rem) (hidx : idx < 519)
    (KS' : KJ impl ret0 Q (JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
      (1792928 + 4 * idx) w v (Vr * Vr) (2 * W lm) Vr n1 n2 n3 rem'))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 po lo co pr lr cr : Nat}
    (h : JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u pcT v w Vr lrb Vo
      o1 o2 o3 rem S0 M0 L1 b1 po lo co pr lr cr)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1815584) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + n1, sp + n1 + 8), (sp + n2, sp + n2 + 8), (sp + n3, sp + n3 + 8)])
    (hrg : T.mem.regions = M0.regions)
    (r1 : T.mem.readLE (sp + n1) 8 = pr) (r2 : T.mem.readLE (sp + n2) 8 = lr)
    (r3 : T.mem.readLE (sp + n3) 8 = cr) (h30 : T.regs 30 = BitVec.ofNat 64 (1792928 + 4 * idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 po) (h1 : T.regs 1 = BitVec.ofNat 64 lo) (h2 : T.regs 2 = BitVec.ofNat 64 co)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 pr) (h5 : T.regs 5 = BitVec.ofNat 64 lr)
    (h6 : T.regs 6 = BitVec.ofNat 64 cr) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  have hsw : ∀ r ∈ [(sp + n1, sp + n1 + 8), (sp + n2, sp + n2 + 8), (sp + n3, sp + n3 + 8)], SW sp r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rcases hr with rfl | rfl | rfl <;> simp only [SW] <;> omega
  have hq : ∀ a, a = sp + 200 ∨ a = sp + 208 ∨ a = sp + 240 ∨ a = sp + 160 → T.mem.readLE a 8 = M0.readLE a 8 :=
    fun a ha => hF.readLE a 8 (by
      simp only [outside_cons, outside_nil, and_true]
      rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega)
  have hn88 : 88 ≤ n1 ∧ n1 + 8 ≤ 848 ∧ 88 ≤ n2 ∧ n2 + 8 ≤ 848 ∧ 88 ≤ n3 ∧ n3 + 8 ≤ 848 := by
    rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hjc.bf hF hrg hsw
  have hlr := h.lrb
  have hlx0 : 0 < lr := len_pos h.nr.2.1 h.nr.2.2.2
  have hcr : 0 < cr := by have := h.nr.1; omega
  have hlo0 : 0 < lo := len_pos h.no.2.1 h.no.2.2.2
  have hco : 0 < co := by have := h.no.1; omega
  obtain ⟨hO, -⟩ := hkeep w po co h.ro hco
  obtain ⟨hZr, hZrk⟩ := hkeep v pr cr h.rr hcr
  have hZn : NV T.mem pr lr cr Vr := NV.keep h.nr hZrk
  have hZr' : BC R L K g sp st zp zc T.mem L1 zzp bp lm (!w) pr cr := hvw ▸ hZr
  have hmono := hsm (lvlL (stLen s.mem st) lm) lr (W lm) (by omega)
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : sqC (lvlL (stLen s.mem st) lm) lr ≤ b1 := by simp only [bodyB, SQ, ML] at hb hmono hrem; omega
  refine sqrB hap hns hnf hsq hkS haS hP hB (v := w) hO hco h.no.1 hZr' hZn (by omega) hcst hidx T hpc hsp h28 rfl
    h30 h0 h1 h2 h3 h4 h5 h6 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres hnv hl' hx hxn hbud
  have hx' : BC R L K g sp st zp zc s'.mem L2 zzp bp lm v pr cr := hvw ▸ hx
  exact KS' s' s'.mem L2 b2 pr lr cr p' l' c'
    { jc := ⟨hsp'.trans hsp, h28'.trans h28, h29'.trans h29, h18'.trans h18, rfl, hB',
        (hslot _ _ (by omega) (by omega)).trans ((hq _ (by omega)).trans hjc.s200),
        (hslot _ _ (by omega) (by omega)).trans ((hq _ (by omega)).trans hjc.s208),
        (hslot _ _ (by omega) (by omega)).trans ((hq _ (by omega)).trans hjc.s240),
        (hslot _ _ (by omega) (by omega)).trans ((hq _ (by omega)).trans hjc.s160), hjc.hi, hjc.hyi,
        hjc.hc, hjc.hu, hjc.hfv, hcb⟩
      epc := hpc', e0 := e0, e1 := e1, e2 := e2, rr := hres, nr := hnv, lrb := hl', ro := hx', no := hxn,
      lob := by omega, so1 := (hslot _ _ (by omega) (by omega)).trans r1,
      so2 := (hslot _ _ (by omega) (by omega)).trans r2, so3 := (hslot _ _ (by omega) (by omega)).trans r3,
      hb := by simp only [bodyB, SQ, ML] at hb hmono hrem ⊢; omega }

end

end FvModexp.Arm64.P2W4
