import FvModexp.Proofs.Arm64.Exp.P2W4LK
import FvModexp.Proofs.Arm64.Exp.P2W4Ret1

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the loop's outer step (agent infra)

`outerStep`: at `LT` with `c = 0` windows left in the current word and `i + 1` words left: the test's stores
`280 := z.ptr`, `112 := z.len`, `TBZ` (not taken: `c - 1 < 0`), `CBZ i` (not taken), `i--` (`208 := i`), the
bounds check (`i < len y`), `yi = y[i]`, `k = 15`, back to `LT` with `c = 16` (nat.go:1249-1253).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

theorem m1_63 : (BitVec.ofNat 64 0 - 1#64).getLsbD 63 = true := by decide

theorem sub1 (i : Nat) (h : i + 1 < 2 ^ 64) : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem outerStep (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (i : Nat)
    (KN : KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i 16) :
    KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV (i + 1) 0 := by
  intro S M L1 b1 yi Z pA lA cA pB lB cB u h
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hi := h.hi
  have hyw := y_words hP h.li.wc i (by omega)
  have hmacc : M.accessible (sp - K) (K + 848) true = true := by
    rw [h.li.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hya : M.accessible yp (8 * yl) false = true := by
    rw [h.li.wc.fr.accessible]; exact hP.2.2.2.2.2.2.2.2.1
  have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.1
  have ya1 : M.accessible (yp + 8 * i) 8 false = true :=
    Memory.accessible_mono _ hya (by omega) (by omega)
  have e7 := h.e7
  have e11 := h.e11
  have hli := h.li
  have hb := h.hb
  have hfv := h.hfv
  have hu := h.hu
  obtain ⟨epc, esp, e28, e29, e18, em, e3, e1, e14, e0, e15, e13, e8, -, e4, e9, e10, -, e12, e2, -, -, -, -, -, -,
    -⟩ := h
  have hyA : Apart yp (8 * yl) (sp - K) (K + 848) := hP.2.2.2.2.2.2.2.1.2.1
  unfold Apart at hyA
  subst em
  have hyw' : S.mem.readLE (yp + i * 8) 8 = Exp.wd (natVal s.mem yp yl) i := by rw [Nat.mul_comm]; exact hyw
  janus_run [m1_63, hyw, ya1, hmacc, sub1 i (by omega)] until [LT]
  refine KN _ _ L1 b1 (Exp.wd (natVal s.mem yp yl) i) Z pA lA cA pB lB cB u
    ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      LI.win hP hli (ws := [(sp + 280, sp + 288), (sp + 112, sp + 120), (sp + 208, sp + 216)]) ?F ?rg ?ws ?r208, by omega, by have := Exp.wd_lt (natVal s.mem yp yl) i; simp only [Exp.B] at this; exact this, by omega, by rw [hu]; omega, ?bud, ?fv⟩
  case F => janus_frame
  case rg => simp only [Memory.regions_writeLE]
  case ws =>
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> omega
  case r208 => rw [Memory.readLE_writeLE_self] <;> omega
  case bud => rw [show 16 + 16 * i = 0 + 16 * (i + 1) by omega]; exact hb
  case fv => rw [← hfv]; rfl
  all_goals first | (janus_simp [hyw']; done) | skip

end

end FvModexp.Arm64.P2W4
