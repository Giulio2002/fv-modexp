import FvModexp.Proofs.Arm64.Exp.P2W4BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): loop body segment B10 — `J10` → back to the loop test (agent infra)

From the fifth `trunc`'s return `0x1b619c`: `yi <<= 4`, `k--`, the reloads (`200`, `stk`, `len y`, `i`, `y.ptr`,
`logM`) and the swap `z, zz = Z5, Z4` (`R3/R1/R14 := Z5`, `R0/R15/R13 := Z4` from slots `280/112/216`) → `LT`
with `c` windows left, `u' = !u`, value `stp Z (yi >> 60)` (nat.go:1103-1104, 1069).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

theorem lsl4_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 60 &&& 18446744073709551600#64 &&& 18446744073709551615#64) =
      BitVec.ofNat 64 (n * 16 % Exp.B) := by
  apply BitVec.eq_of_toNat_eq
  have h := Janus.Contracts.Iface.lsl_toNat (BitVec.ofNat 64 n) 4 (by decide)
  rw [BitVec.toNat_and, BitVec.toNat_and]
  change (_ &&& 18446744073709551600) &&& 18446744073709551615 = _
  rw [show (64 - 4 : Nat) = 60 from rfl, show (2 ^ 64 - 2 ^ 4 : Nat) = 18446744073709551600 from rfl] at h
  rw [h, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat, Exp.B]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_mod, Nat.mod_mod, Nat.mul_comm]

theorem sub2_ofNat (kk : Nat) :
    BitVec.ofNat 64 ((18446744073709551614 + kk) % 18446744073709551616) = BitVec.ofNat 64 kk - 2#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_sub]
  omega

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat}
    {mlC : Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

/-- the loop invariant after a body -/
theorem li10 {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 po lo co pr lr cr : Nat}
    (h : J10 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1 po lo co
      pr lr cr) :
    LI R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp kk i (!u) pr lr cr po lo co
      (Z5 lm (natVal s.mem xp xl) Z yi) :=
  { wc := h.jc.bf.wc, esl := h.jc.bf.esl, s200 := h.jc.s200, s208 := h.jc.s208, tz := h.jc.bf.tz, la := h.lrb,
    lac := h.nr.1, lbc := h.no.1, va := h.nr.2.1, na := h.nr.2.2.1, ca := h.rr,
    cb := by rw [Bool.not_not]; exact h.ro, zo := h.nr.2.2.2,
    cb0 := by have := len_pos h.no.2.1 h.no.2.2.2; have := h.no.1; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B10** -/
theorem segB10 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (KN : KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c) :
    KJ impl ret0 Q (J10 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u) := by
  intro S M L1 b1 po lo co pr lr cr h
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 848) true = true := by
    rw [h.jc.bf.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hesl := h.jc.bf.esl
  have r784 : M.readLE (sp + 784) 8 = st := hesl.2.2.2.2.2.2.2.2.1
  have r816 : M.readLE (sp + 816) 8 = yp := hesl.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r824 : M.readLE (sp + 824) 8 = yl := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r840 : M.readLE (sp + 840) 8 = lm := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r200 := h.jc.s200
  have r208 := h.jc.s208
  have r240 := h.jc.s240
  have r160 := h.jc.s160
  have r280 := h.so1
  have r112 := h.so2
  have r216 := h.so3
  have hst48 := h.jc.bf.wc.sok.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyp : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.1
  have hi := h.jc.hi
  have hc := h.jc.hc
  have hyi := h.jc.hyi
  have hco : 0 < co := by have := len_pos h.no.2.1 h.no.2.2.2; have := h.no.1; omega
  have hf2 := BC.facts hP h.jc.bf h.ro hco
  have h240 := hf2.1
  have h248 := (hf2.2.1 hco).2.2.2
  have hlo := h.no.1
  have hli := li10 h
  have hu := h.jc.hu
  have hfv := h.jc.hfv
  have hb := h.hb
  have hsh := lsl4_ofNat yi hyi
  have hs2 := sub2_ofNat kk
  obtain ⟨⟨esp, e28, e29, e18, em, -⟩, epc, e0, e1, e2, -⟩ := h
  subst em
  janus_run [hmacc, r784, r816, r824, r840, r200, r208, r240, r160, r280, r112, r216, hsh] until [LT]
  refine KN _ S.mem L1 b1 (yi * 16 % Exp.B) (Z5 lm (natVal s.mem xp xl) Z yi) pr lr cr po lo co (!u)
    ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hli, hi,
      by simp only [Exp.B]; exact Nat.mod_lt _ (by decide), by omega, ?hu, hb, ?fv⟩
  case hu => cases u <;> simp only [Bool.not_false, Bool.not_true, true_iff, false_iff, Bool.false_eq_true] at hu ⊢ <;> omega
  case fv => rw [← hfv, outer_succ]; rfl
  all_goals (janus_simp [hsh, hs2] <;> omega)

end

end FvModexp.Arm64.P2W4
