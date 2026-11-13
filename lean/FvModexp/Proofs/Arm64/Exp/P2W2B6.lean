import FvModexp.Proofs.Arm64.Exp.P2W2BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): loop body segment B6 — `J6` → back to the loop test (agent infra)

From the third `trunc`'s return `1796480`: `yi <<= 2`, `k--`, the reloads (`200`, `stk`, `len y`, `i`, `y.ptr`,
`logM`) and the swap `z, zz = Z3, Z2` (`R3/R1/R14 := Z3`, `R0/R13/R15 := Z2` from slots `280/112/216`) → `LT`
with `c` windows left, `u' = !u`, value `stp Z (yi >> 62)` (nat.go:1245-1247, 1223).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

theorem lsl2_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n).rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64) =
      BitVec.ofNat 64 (n * 4 % Exp.B) := by
  apply BitVec.eq_of_toNat_eq
  have h := Janus.Contracts.Iface.lsl_toNat (BitVec.ofNat 64 n) 2 (by decide)
  rw [BitVec.toNat_and, BitVec.toNat_and]
  change (_ &&& 18446744073709551612) &&& 18446744073709551615 = _
  rw [show (64 - 2 : Nat) = 62 from rfl, show (2 ^ 64 - 2 ^ 2 : Nat) = 18446744073709551612 from rfl] at h
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
theorem li6 {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p2 l2 c2 p3 l3 c3 : Nat}
    (h : J6 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1 p2 l2 c2
      p3 l3 c3) :
    LI R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp kk i (!u) p3 l3 c3 p2 l2 c2
      (Z3 lm (natVal s.mem xp xl) Z yi) :=
  { wc := h.jc.bf.wc, esl := h.jc.bf.esl, s200 := h.jc.s200, s208 := h.jc.s208, tz := h.jc.bf.tz, la := h.l3b,
    lac := h.n3.1, lbc := h.n2.1, va := h.n3.2.1, na := h.n3.2.2.1, ca := h.r3,
    cb := by rw [Bool.not_not]; exact h.r2, zo := h.n3.2.2.2,
    cb0 := by have := len_pos h.n2.2.1 h.n2.2.2.2; have := h.n2.1; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B6** -/
theorem segB6 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (KN : KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c) :
    KJ impl ret0 Q (J6 R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u) := by
  intro S M L1 b1 p2 l2 c2 p3 l3 c3 h
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [h.jc.bf.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hesl := h.jc.bf.esl
  have r496 : M.readLE (sp + 496) 8 = st := hesl.2.2.2.2.2.2.2.2.1
  have r528 : M.readLE (sp + 528) 8 = yp := hesl.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r536 : M.readLE (sp + 536) 8 = yl := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r552 : M.readLE (sp + 552) 8 = lm := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r200 := h.jc.s200
  have r208 := h.jc.s208
  have r240 := h.jc.s240
  have r160 := h.jc.s160
  have r280 := h.s280
  have r112 := h.s112
  have r216 := h.s216
  have hst48 := h.jc.bf.wc.sok.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyp : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.1
  have hi := h.jc.hi
  have hc := h.jc.hc
  have hyi := h.jc.hyi
  have hc2 : 0 < c2 := by have := len_pos h.n2.2.1 h.n2.2.2.2; have := h.n2.1; omega
  have hf2 := BC.facts hP h.jc.bf h.r2 hc2
  have h240 := hf2.1
  have h248 := (hf2.2.1 hc2).2.2.2
  have hl2 := h.n2.1
  have hli := li6 h
  have hu := h.jc.hu
  have hfv := h.jc.hfv
  have hb := h.hb
  have hsh := lsl2_ofNat yi hyi
  have hs2 := sub2_ofNat kk
  obtain ⟨⟨esp, e28, e29, e18, em, -⟩, epc, e0, e1, e2, -⟩ := h
  subst em
  janus_run [hmacc, r496, r528, r536, r552, r200, r208, r240, r160, r280, r112, r216, hsh] until [LT]
  refine KN _ S.mem L1 b1 (yi * 4 % Exp.B) (Z3 lm (natVal s.mem xp xl) Z yi) p3 l3 c3 p2 l2 c2 (!u)
    ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hli, hi,
      by simp only [Exp.B]; exact Nat.mod_lt _ (by decide), by omega, ?hu, hb, ?fv⟩
  case hu => cases u <;> simp only [Bool.not_false, Bool.not_true, true_iff, false_iff, Bool.false_eq_true] at hu ⊢ <;> omega
  case fv => rw [← hfv, outer_succ]; rfl
  all_goals (janus_simp [hsh, hs2] <;> omega)

end

end FvModexp.Arm64.P2W2
