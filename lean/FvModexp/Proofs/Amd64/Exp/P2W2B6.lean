import FvModexp.Proofs.Amd64.Exp.P2W2BJ
import FvModexp.Proofs.Amd64.Exp.P2W2Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): loop body segment B6 — `J6` → back to the loop test (agent divmc s73; amd64
twin of agent infra's `Arm64.P2W2B6`)

From the third `trunc`'s return fn+0x771: `yi <<= 2` (`DX := [0x98] << 2`), `k--` (`R10 := [0xf0] - 1`), the reloads
(`DI = len y`, `R11 = i`, `R13 = stk`, `AX = logM`, `DX = y.ptr`) and the swap `z, zz = Z3, Z2` (`R9/SI/R12 := Z3`,
`R8/CX/R15 := Z2` from the slots `0x118/0x68/0xd0`) → `LT` with `c` windows left, `u' = !u`, value
`stp Z (yi >> 62)` (nat.go:1245-1247, 1223).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

theorem shl2_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 2 = BitVec.ofNat 64 (n * 2 ^ 2 % Exp.B) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Exp.B]
  rw [Nat.mod_mul_mod, Nat.mod_mod]

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

/-- the loop invariant after a body -/
theorem li6 {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p2 l2 c2 p3 l3 c3 : Nat}
    (h : J6 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1 p2 l2 c2 p3 l3 c3) :
    LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i (!u) p3 l3 c3 p2 l2 c2
      (Z3 lm (natVal s.mem xp xl) Z yi) :=
  { wc := h.jc.bf.wc, esl := h.jc.bf.esl, sc0 := h.jc.sc0, sc8 := h.jc.sc8, tz := h.jc.bf.tz, la := h.l3b,
    lac := h.n3.1, lbc := h.n2.1, va := h.n3.2.1, na := h.n3.2.2.1, ca := h.r3,
    cb := by rw [Bool.not_not]; exact h.r2, zo := h.n3.2.2.2,
    cb0 := by have := len_pos h.n2.2.1 h.n2.2.2.2; have := h.n2.1; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B6** -/
theorem segB6 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    (KN : KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c) :
    KJ impl ret0 Q (J6 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) := by
  intro S M L1 b1 p2 l2 c2 p3 l3 c3 h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x238 ≤ 2 ^ 48 := hce.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ hce.2.2.2.1
  have hesl := h.jc.bf.esl
  have q208 : M.readLE (sp + 0x208) 8 = st := hesl.2.2.2.2.2.2.2.2.1
  have q1d8 : M.readLE (sp + 0x1d8) 8 = yp := hesl.2.2.2.2.2.2.2.2.2.2.2.2.1
  have q1e0 : M.readLE (sp + 0x1e0) 8 = yl := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have q228 : M.readLE (sp + 0x228) 8 = lm := hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qc8 := h.jc.sc8
  have qf0 := h.jc.sf0
  have q98 := h.jc.s98
  have q118 := h.s118
  have q68 := h.s68
  have qd0 := h.sd0
  have hi := h.jc.hi
  have hc := h.jc.hc
  have hyi := h.jc.hyi
  have hli := li6 h
  have hu := h.jc.hu
  have hfv := h.jc.hfv
  have hb := h.hb
  have hsh := shl2_ofNat yi
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
      (Z3 lm (natVal s.mem xp xl) Z yi)) := ⟨hli⟩
  clear h hce hesl hli hP
  subst em
  refine SegProg.lift P2W2Seg.codeIn (r := BitVec.ofNat 64 LT) ?_
  janus64_run [hwaccF, q208, q1d8, q1e0, q228, qc8, qf0, q98, q118, q68, qd0, hsh] until [LT]
  refine KN _ S.mem L1 b1 (yi * 2 ^ 2 % Exp.B) (Z3 lm (natVal s.mem xp xl) Z yi) p3 l3 c3 p2 l2 c2 (!u)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLH.h, hi,
      by simp only [Exp.B]; exact Nat.mod_lt _ (by decide), by omega, ?hu, hb, ?fv⟩
  case hu => cases u <;> simp only [Bool.not_false, Bool.not_true, true_iff, false_iff, Bool.false_eq_true] at hu ⊢ <;> omega
  case fv => rw [← hfv, outer_succ]; rfl
  all_goals first
    | exact efs
    | (janus64_simp; done)
