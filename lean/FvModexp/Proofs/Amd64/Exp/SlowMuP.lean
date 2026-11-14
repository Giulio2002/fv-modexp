import FvModexp.Proofs.Amd64.Exp.SlowCP

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): `nat.mul`'s Q-form precondition `MPre` for `zz.mul(stk, z, x)` at a call from the slow
frame (agent expmc s81; twin of `sqrPreS`)

Callee entry `S'` (`RSP = sp - 8`, window `[sp - 8 - W, sp - 8 + 88)`); the destination `zz` (`DL`), the first
operand the loop's `z` (`LN`, possibly empty), the second operand the input `x` (entry facts `OE` + `XFacts`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

/-- the slow frame's outer ranges cover a callee window (context-free, for `WC.globals`) -/
theorem glW {S' : State} {sp K W A st : Nat} (tsp : (S'.regs 4).toNat = sp - 8) (hWK : W ≤ K) (hK : K + 8 ≤ sp)
    (hA : A ≤ 0x70) : ∀ a n, Outside a n [(sp - 8 - K, sp + 0x220), (st, st + 24)] → Outside a n (win S' W A) := by
  intro a n ho; simp only [win, tsp, outside_cons, outside_nil, and_true] at ho ⊢; omega

/-- apart from the slow window → outside a callee window (context-free) -/
theorem apWin {S' : State} {sp K W A : Nat} (tsp : (S'.regs 4).toNat = sp - 8) (hWK : W ≤ K) (hK : K + 8 ≤ sp)
    (hA : A ≤ 0x70) {p n : Nat} (h : Apart p n (sp - 8 - K) (K + 0x228)) : Outside p n (win S' W A) := by
  unfold Apart at h; simp only [win, tsp, outside_cons, outside_nil, and_true]; omega

theorem le8 {l c p : Nat} (h : l ≤ c) : p + 8 * l ≤ p + 8 * c := Nat.add_le_add_left (Nat.mul_le_mul_left 8 h) p

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.mul`'s Q-form precondition** at the callee entry `S'` (`RSP = sp - 8`): `zz.mul(stk, z, x)` -/
theorem mulPreS (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {W : Nat} (hWK : W ≤ K)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M) {pd cd px lx cx vx : Nat} (hd : DL R L st zp zc M L1 pd cd)
    (hx : LN R L st zp zc M L1 px lx cx vx) (hdx : Pw px cx pd cd) (hX : NHyp.XFacts R L xp xl xc)
    (hlx : lx ≤ 2 ^ 12) (hmW : mulW64 lx xl ≤ W) (hs16 : ℓ + 4 * (lx + xl) + 64 ≤ 2 ^ 16) {H : Nat}
    (hH : ℓ + 4 * (lx + xl) + 64 ≤ H) (hb : mulCQ lx xl + stkR H M st ≤ b1) :
    Q.NatMul.MPre R b1 H L1 W pd cd st px lx cx xp xl xc S' := by
  have hk := hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.1
  have hadx : M.accessible Callees.adxAddr 1 false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.1
  have hK8 : K ≤ sp - 8 := Nat.le_sub_of_add_le hk.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := W) (above := 88) hWK (by decide)
    (Nat.le_trans hWK hK8)
  have hgl := hw.globals hP (w := win S' W 88) (glW tsp hWK hk.2.2.1 (by decide))
  have hsk := stkS hP hw tsp tg tfs fm (W := W) (A := 88) hWK (by decide)
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxacc : s.mem.accessible xp (8 * xl) false = true := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxO : OE R L sp K st s.mem xp (8 * xl) := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hxL, hxW, hxst, hxfr⟩ := hxO
  have hxfM := free_apart hw hxL hxfr
  simp only [free] at hxfM
  obtain ⟨⟨hX1, hX2, hX3⟩, hX4⟩ := hX
  have hxw := apWin tsp hWK hk.2.2.1 (by decide : 88 ≤ 0x70) (Loc.win hP hx.1.2.2.1) (W := W)
  have hdw := apWin tsp hWK hk.2.2.1 (by decide : 88 ≤ 0x70) (Loc.win hP hd.2.2.1) (W := W)
  have hxW' := apWin tsp hWK hk.2.2.1 (by decide : 88 ≤ 0x70) hxW (W := W)
  subst fm
  refine ⟨hce, hmW, hsv, hgl, hwT, ⟨⟨hx.2.1, hx.1.1, hlx, fun h0 => ?_, fun hc => ⟨(hx.1.2.1 hc).2.1,
      (hx.1.2.1 hc).2.2.2⟩, fun h0 => ⟨?_, DL.sep hP hx.1 (Nat.lt_of_lt_of_le h0 hx.2.1)
      (Nat.mul_le_mul_left 8 hx.2.1)⟩⟩,
    ⟨hX1, hX2, Nat.le_trans hxl (by decide), fun _ => by rw [hw.fr.accessible]; exact hxacc, fun hc => ⟨hw.le.held (hX3 hc).1,
      (hX3 hc).2⟩, fun h0 => ⟨?_, hxst.symm, by simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; exact hxfM,
      hX4 h0⟩⟩,
    ⟨hd.1, hd.2.1, ?_, fun hc => ⟨?_, ?_, DL.sep hP hd hc (Nat.le_refl _)⟩,
      Or.inr fun hc hl => apR (hdx (Nat.lt_of_lt_of_le hl hx.2.1) hc).symm (Nat.mul_le_mul_left 8 hx.2.1),
      Or.inr fun hc _ => (Loc.ap hP hd.2.2.1 hc).2.2.2.2.1⟩, by rw [hlen]; exact hs16⟩,
    hsk, ⟨by rw [hlen]; exact hH, hb⟩, hadx, by rw [tg]; exact hw.inv⟩
  · obtain ⟨-, -, xacc, -⟩ := hx.1.2.1 (Nat.lt_of_lt_of_le h0 hx.2.1)
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ xacc (Nat.le_refl _)
      (le8 hx.2.1))
  · exact hxw.of_sub (Nat.le_refl _) (le8 hx.2.1)
  · exact hxW'
  · exact hdw
  · simp only [Q.NatSqr.guard, tg]; exact (Loc.ap hP hd.2.2.1 hc).2.2.1
  · simp only [Q.NatSqr.tls, tfs]; exact Loc.tls hP hd.2.2.1 hc

end

end FvModexp.Amd64.ExpSlow
