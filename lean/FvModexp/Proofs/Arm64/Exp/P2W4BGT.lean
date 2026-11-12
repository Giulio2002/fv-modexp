import FvModexp.Proofs.Arm64.Exp.P2W4BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the body's generic `trunc` step (agent infra)

`callT`: at the `nat.trunc` entry (`z = z.trunc(z, logM)` in place, return `fn + 4 idx`) from a join point
`JX pcQ v w Vr lrb Vo o1 o2 o3 rem` (the product just returned): the continuation gets
`JX (fn + 4 idx) v w (Vr mod 2^logM) w Vo o1 o2 o3 rem'` for any `rem' + tC ≤ rem`. Shared by the five trunc
segments `B1/B3/B5/B7/B9` (window-4 generalisation of the window-2 `callB1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)
open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem callT (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    {pcQ : Nat} {v w : Bool} {Vr lrb Vo o1 o2 o3 rem rem' idx : Nat} (hvw : v = !w) (hlrb : lrb ≤ 2 * W lm)
    (ho : 88 ≤ o1 ∧ o1 + 8 ≤ 848 ∧ 88 ≤ o2 ∧ o2 + 8 ≤ 848 ∧ 88 ≤ o3 ∧ o3 + 8 ≤ 848)
    (hrem : rem' + P2Pre.tC lm ≤ rem) (hidx : idx < 519)
    (KT : KJ impl ret0 Q (JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
      (1792928 + 4 * idx) v w (Vr % 2 ^ lm) (W lm) Vo o1 o2 o3 rem'))
    {S0 : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 po lo co pr lr cr : Nat}
    (h : JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u pcQ v w Vr lrb Vo
      o1 o2 o3 rem S0 M L1 b1 po lo co pr lr cr)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1786000) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = r29) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = M)
    (h30 : T.regs 30 = BitVec.ofNat 64 (1792928 + 4 * idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 pr) (h1 : T.regs 1 = BitVec.ofNat 64 lr) (h2 : T.regs 2 = BitVec.ofNat 64 cr)
    (h3 : T.regs 3 = BitVec.ofNat 64 pr) (h4 : T.regs 4 = BitVec.ofNat 64 lr) (h5 : T.regs 5 = BitVec.ofNat 64 cr)
    (h6 : T.regs 6 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hB := h.jc.bf
  have hb := h.hb
  have hcb := h.jc.hcb
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
  have hlr := h.lrb
  have hlx0 : 0 < lr := len_pos h.nr.2.1 h.nr.2.2.2
  have hcr : 0 < cr := by have := h.nr.1; omega
  have hlo0 : 0 < lo := len_pos h.no.2.1 h.no.2.2.2
  have hco : 0 < co := by have := h.no.1; omega
  have hrr : BC R L K g sp st zp zc M L1 zzp bp lm (!w) pr cr := hvw ▸ h.rr
  refine trB hap hns hnf htr hkT haT hP hB h.rr h.nr (by omega) (by simp only [bodyB] at hb; omega) hidx T hpc
    hsp h28 hm h30 h0 h1 h2 h3 h4 h5 h6 ?_
  intro s' L2 b2 l' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres hnv hl' hkeep hbud
  obtain ⟨hO, hOk⟩ := hkeep w po co h.ro hco (bc_apart hP hB h.ro hrr hco hcr)
  have hjc := h.jc
  exact KT s' s'.mem L2 b2 po lo co pr l' cr
    { jc := hjc.call (hsp'.trans (hsp.trans hjc.esp.symm)) (h28'.trans (h28.trans hjc.e28.symm))
        (h29'.trans (h29.trans hjc.e29.symm)) (h18'.trans (h18.trans hjc.e18.symm)) rfl hB'
        hslot,
      epc := hpc', e0 := e0, e1 := e1, e2 := e2, rr := hres, nr := hnv, lrb := hl', ro := hO,
      no := NV.keep h.no hOk, lob := h.lob,
      so1 := (hslot _ _ (by omega) (by omega)).trans h.so1,
      so2 := (hslot _ _ (by omega) (by omega)).trans h.so2,
      so3 := (hslot _ _ (by omega) (by omega)).trans h.so3,
      hb := by simp only [bodyB] at hb ⊢; omega }

end

end FvModexp.Arm64.P2W4
