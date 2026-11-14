import FvModexp.Proofs.Amd64.Exp.P2W4BJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): loop body segment B10 — `J10` → back to the loop test (agent divmc s77, port of divmc s73; amd64
twin of agent infra's `Arm64.P2W4B10`)

From the fifth `trunc`'s return fn+0x82a: `yi <<= 4` (`DX := [0x98] << 4`), `k--` (`R15 := [0xf0] - 1`), the reloads
(`DI = y.ptr`, `R10 = stk`, `R11 = i`, `R12 = len y`, `AX = logM`) and the swap `z, zz = Z5, Z4` (`R9/SI/R13 := Z5`,
`R8/CX/DX := Z4` from the slots `0x120/0x68/0xd8`) → `LT` with `c` windows left, `u' = !u`, value
`stp Z (yi >> 60)` (nat.go:1103-1104, 1069).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

theorem shl4_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (n * 2 ^ 4 % Exp.B) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Exp.B]
  rw [Nat.mod_mul_mod, Nat.mod_mod]

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

/-- the loop invariant after a body -/
theorem li10 {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p2 l2 c2 p3 l3 c3 : Nat}
    (h : J10 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1 p2 l2 c2 p3 l3 c3) :
    LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i (!u) p3 l3 c3 p2 l2 c2
      (Z5 lm (natVal s.mem xp xl) Z yi) :=
  { wc := h.jc.bf.wc, esl := h.jc.bf.esl, sc0 := h.jc.sc0, sc8 := h.jc.sc8, tz := h.jc.bf.tz, la := h.lrb,
    lac := h.nr.1, lbc := h.no.1, va := h.nr.2.1, na := h.nr.2.2.1, ca := h.rr,
    cb := by rw [Bool.not_not]; exact h.ro, zo := h.nr.2.2.2,
    cb0 := by have := len_pos h.no.2.1 h.no.2.2.2; have := h.no.1; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B10** -/
theorem segB10 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (KN : KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c) :
    KJ impl ret0 Q (J10 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) := by
  intro S M L1 b1 p2 l2 c2 p3 l3 c3 h
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ hce.2.2.2.1
  have hesl := h.jc.bf.esl
  have q208 : M.readLE (sp + 0x330) 8 = st := hesl.2.2.2.2.2.2.2.2.1
  have q1d8 : M.readLE (sp + 0x300) 8 = yp := hesl.2.2.2.2.2.2.2.2.2.2.2.2.1
  have q1e0 : M.readLE (sp + 0x308) 8 = yl := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have q228 : M.readLE (sp + 0x350) 8 = lm := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qc8 := h.jc.sc8
  have qf0 := h.jc.sf0
  have q98 := h.jc.s98
  have q118 := h.so1
  have q68 := h.so2
  have qd0 := h.so3
  have hi := h.jc.hi
  have hc := h.jc.hc
  have hyi := h.jc.hyi
  have hli := li10 h
  have hu := h.jc.hu
  have hfv := h.jc.hfv
  have hb := h.hb
  have hsh := shl4_ofNat yi
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
  have hLH : HdM (LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i (!u) p3 l3 c3 p2 l2 c2
      (Z5 lm (natVal s.mem xp xl) Z yi)) := ⟨hli⟩
  clear h hce hesl hli hP
  subst em
  janus64_run [hwaccF, q208, q1d8, q1e0, q228, qc8, qf0, q98, q118, q68, qd0, hsh] until [LT]
  refine KN _ S.mem L1 b1 (yi * 2 ^ 4 % Exp.B) (Z5 lm (natVal s.mem xp xl) Z yi) p3 l3 c3 p2 l2 c2 (!u)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLH.h, hi,
      by simp only [Exp.B]; exact Nat.mod_lt _ (by decide), by omega, ?hu, hb, ?fv⟩
  case hu => cases u <;> simp only [Bool.not_false, Bool.not_true, true_iff, false_iff, Bool.false_eq_true] at hu ⊢ <;> omega
  case fv => rw [← hfv, outer_succ]; rfl
  all_goals first
    | exact efs
    | (janus64_simp; done)
