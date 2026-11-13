import FvModexp.Proofs.Arm64.Exp.P2W2BMu
import FvModexp.Proofs.Arm64.Exp.P2W2BTr

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the loop body's join points `J1 … J6` (agent infra)

The body (nat.go:1235-1247, entered from the loop test with `c + 1` windows left, i.e. `k = c`) makes six calls:
`zz = zz.sqr(z)` (return `1796288`), `trunc` (`1796308`), `zz = zz.sqr(z)` (`1796352`), `trunc` (`1796372`),
`zz = zz.mul(z, powers[yi >> 62])` (`1796460`), `trunc` (`1796480`), swapping `z`/`zz` after each product.
`Jk` = the facts at the return of call `k`: the common part `JC` (stack/FP/g regs, `BF`, the slots `200 = kk - 2`,
`208 = i`, `240 = c`, `160 = yi`, bounds, parity, model, `cst ≤ b`) plus the live buffers with their classes,
values and the result registers, and the budget `bodyB + rk ≤ b1 + cst` (`rk` = the bound of the calls still to
come). Values: `Z1 = Z² mod 2^logM`, `Z2 = Z1² mod 2^logM`, `Z3 = Z2·powers[d] mod 2^logM = stp Z d`
(`d = yi >> 62`). Each segment `Bk` (one module each) proves `KJ(k+1) → KJk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the budget part common to the body: what the loop needs after this body -/
@[reducible] def bodyB (b : Nat) (s : State) (st lm : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c : Nat) : Nat :=
  b + (c + 32 * i) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm + P2Pre.tC lm

/-- the `sqr` / `mul` bounds at the loop level -/
@[reducible] def SQ (s : State) (st lm : Nat) (sqC : Nat → Nat) : Nat := sqC (W lm)
@[reducible] def ML (s : State) (st lm : Nat) (mlC : Nat → Nat → Nat) : Nat :=
  mlC (W lm) (W lm)

/-- the window `d = yi >> 62` -/
@[reducible] def dOf (yi : Nat) : Nat := yi / 2 ^ 62

/-- the body's values -/
@[reducible] def Z1 (lm Z : Nat) : Nat := Z * Z % 2 ^ lm
@[reducible] def Z2 (lm Z : Nat) : Nat := Z1 lm Z * Z1 lm Z % 2 ^ lm
@[reducible] def Z3 (lm X Z yi : Nat) : Nat := Z2 lm Z * Exp.p2Pow lm X (dOf yi) % 2 ^ lm

theorem Z3_eq (lm X Z yi : Nat) : Z3 lm X Z yi = stp lm X Z (yi / 2 ^ (64 - 2)) := rfl

/-- the common facts at every join point of the body -/
structure JC (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  esp : S.sp = BitVec.ofNat 64 sp
  e28 : S.regs 28 = BitVec.ofNat 64 g
  e29 : S.regs 29 = r29
  e18 : S.regs 18 = s.regs 18
  em : S.mem = M
  bf : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp
  s200 : M.readLE (sp + 200) 8 = (BitVec.ofNat 64 kk - 2#64).toNat
  s208 : M.readLE (sp + 208) 8 = i
  s240 : M.readLE (sp + 240) 8 = c
  s160 : M.readLE (sp + 160) 8 = yi
  hi : i < yl
  hyi : yi < 2 ^ 64
  hc : c < 32
  hu : u = true ↔ (c + 1 + kk) % 2 = 1
  hfv : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i yi (c + 1) Z = FV
  hcb : cst ≤ b

/-- `JC` through a step keeping the slots `[sp + 88, sp + 560)` (a callee) -/
theorem JC.call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm ret : Nat}
    {s : State} {r29 : BitVec 64} {zzp bp kk cst FV : Nat} {sqC : Nat → Nat} {mlC : Nat → Nat → Nat}
    {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (h : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1)
    {S' : State} {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (esp : S'.sp = S.sp) (e28 : S'.regs 28 = S.regs 28) (e29 : S'.regs 29 = S.regs 29) (e18 : S'.regs 18 = S.regs 18)
    (em : S'.mem = M') (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M' L2 b2 zzp bp)
    (hk : ∀ a k, sp + 88 ≤ a → a + k ≤ sp + 560 → M'.readLE a k = M.readLE a k) :
    JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S' M' L2 b2 :=
  ⟨esp.trans h.esp, e28.trans h.e28, e29.trans h.e29, e18.trans h.e18, em, hB,
    (hk _ _ (by omega) (by omega)).trans h.s200, (hk _ _ (by omega) (by omega)).trans h.s208,
    (hk _ _ (by omega) (by omega)).trans h.s240, (hk _ _ (by omega) (by omega)).trans h.s160, h.hi, h.hyi, h.hc,
    h.hu, h.hfv, h.hcb⟩

/-- the own stores of the body: window slots off `ESl`, `200`, `208`, the result slots and the table headers -/
@[reducible] def SW (sp : Nat) (r : Nat × Nat) : Prop :=
  sp + 96 ≤ r.1 ∧ r.1 ≤ r.2 ∧ (r.2 ≤ sp + 200 ∨ (sp + 216 ≤ r.1 ∧ r.2 ≤ sp + 256) ∨
    (sp + 280 ≤ r.1 ∧ r.2 ≤ sp + 320) ∨ (sp + 440 ≤ r.1 ∧ r.2 ≤ sp + 448))

/-- `ESl` through stores that keep exactly the slots it reads -/
theorem ESl.keep2 {M1 M3 : Memory} {sp st : Nat} {r29 : BitVec 64} {ret zp zc xp xl xc yp yl lm len0 : Nat}
    (h : ESl M1 sp st r29 ret zp zc xp xl xc yp yl lm len0)
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 95 ≤ a ∧ a + k ≤ sp + 96 ∨ sp + 256 ≤ a ∧ a + k ≤ sp + 280 ∨
      sp + 416 ≤ a ∧ a + k ≤ sp + 440 ∨ sp + 448 ≤ a ∧ a + k ≤ sp + 456 ∨ sp + 472 ≤ a ∧ a + k ≤ sp + 560) →
      M3.readLE a k = M1.readLE a k)
    (hsp : 8 ≤ sp) : ESl M3 sp st r29 ret zp zc xp xl xc yp yl lm len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3,
    (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6,
    (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9,
    (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12,
    (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15,
    (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18,
    (hk _ _ (by omega)).trans a19⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {ret : Nat}

set_option maxRecDepth 20000 in
/-- `BF` and every buffer (class, bytes) through the body's own window stores (`SW`) -/
theorem BF.win (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp bp : Nat} (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp)
    {M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ r ∈ ws, SW sp r) :
    BF R L K g sp st zp zc xp xl xc yp yl lm ret s M' L1 b1 zzp bp ∧
    (∀ a k, (a + k ≤ sp + 96 ∨ sp + 560 ≤ a ∨ (sp + 200 ≤ a ∧ a + k ≤ sp + 216) ∨
      (sp + 256 ≤ a ∧ a + k ≤ sp + 280) ∨ (sp + 320 ≤ a ∧ a + k ≤ sp + 440) ∨ sp + 448 ≤ a) →
      M'.readLE a k = M.readLE a k) ∧
    (∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp bp lm w q d → 0 < d →
      BC R L K g sp st zp zc M' L1 zzp bp lm w q d ∧
        ∀ a k, q ≤ a → a + k ≤ q + 8 * d → M'.readLE a k = M.readLE a k) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a k, (a + k ≤ sp + 96 ∨ sp + 560 ≤ a ∨ (sp + 200 ≤ a ∧ a + k ≤ sp + 216) ∨
      (sp + 256 ≤ a ∧ a + k ≤ sp + 280) ∨ (sp + 320 ≤ a ∧ a + k ≤ sp + 440) ∨ sp + 448 ≤ a) →
      M'.readLE a k = M.readLE a k := fun a k ha =>
    hF.readLE a k (outside_of_forall fun r hr => by have := hws r hr; simp only [SW] at this; omega)
  have hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w := hF.accessible
  have e0 : stW M' st = stW M st := hrd _ _ (by omega)
  have e1 : stLen M' st = stLen M st := hrd _ _ (by omega)
  have e2 : stCap M' st = stCap M st := hrd _ _ (by omega)
  have hbW := scr_win hP hB.tz.bscr
  unfold Apart at hbW
  refine ⟨⟨WC.win hP hB.wc hF hrg (fun r hr => by have := hws r hr; simp only [SW] at this; omega),
    ESl.keep2 hB.esl (fun a k ha => hrd a k (by omega)) (by omega),
    hB.tz.keep hacc (LiveExt.refl R L1) e0 e1 e2 (fun a k ha => hrd a k (by omega))⟩, hrd, fun w q d hq hd => ?_⟩
  have hqW := BC.win hP hB.tz hq hd
  unfold Apart at hqW
  exact ⟨hq.keep hacc (LiveExt.refl R L1) e0 e1 e2, fun a k h1 h2 => hrd a k (by omega)⟩

/-- `NV` through a step keeping the bytes of `p[0:c]` -/
theorem NV.keep {M M' : Memory} {p l c v : Nat} (h : NV M p l c v)
    (hk : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k) : NV M' p l c v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨v1, v2⟩ := nv_keep (M := M) (M' := M') (p := p) (l := l) fun a k a1 a2 => hk a k a1 (by omega)
  exact ⟨h1, v1.trans h2, v2 h3, h4⟩

end

theorem bit63_c {c : Nat} (h : c < 2 ^ 63) : (BitVec.ofNat 64 c).getLsbD 63 = false := by
  rw [BitVec.getLsbD_ofNat]; simp only [show (63 : Nat) < 64 from by decide, decide_true, Bool.true_and]
  exact Nat.testBit_lt_two_pow h

theorem sub1c (i : Nat) (h : i + 1 < 2 ^ 64) : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem outer_succ (step : Nat → Nat → Nat) (y K i yi c z : Nat) :
    Exp.outerLoop 2 step y K i yi (c + 1) z =
      Exp.outerLoop 2 step y K i ((yi * 2 ^ 2) % Exp.B) c (step z (yi / 2 ^ (64 - 2))) := by
  cases i <;> rfl

/-! ## The join points (`Jk` at the return of call `k`; `KJk` = their continuations) -/

/-- after `zz = zz.sqr(z)` (ra `1796288`): result `(p1, l1, c1)` (class `!u`, `Z²`); `A = (pA, lA, cA)` (class `u`,
slots `280/112/224`) -/
structure J1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 pA lA cA p1 l1 c1 : Nat) :
    Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 1796288
  e0 : S.regs 0 = BitVec.ofNat 64 p1
  e1 : S.regs 1 = BitVec.ofNat 64 l1
  e2 : S.regs 2 = BitVec.ofNat 64 c1
  r1 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z * Z)
  l1b : l1 ≤ 2 * W lm
  ca : BC R L K g sp st zp zc M L1 zzp bp lm u pA cA
  lac : lA ≤ cA
  ca0 : 0 < cA
  s280 : M.readLE (sp + 280) 8 = pA
  s112 : M.readLE (sp + 112) 8 = lA
  s224 : M.readLE (sp + 224) 8 = cA
  hb : bodyB b s st lm sqC mlC i c + (SQ s st lm sqC + ML s st lm mlC + 3 * P2Pre.tC lm) ≤ b1 + cst

/-- after the first `trunc` (ra `1796308`): `(p1, l1, c1)` holds `Z1`, `l1 ≤ w` -/
structure J2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 pA lA cA p1 l1 c1 : Nat) :
    Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 1796308
  e0 : S.regs 0 = BitVec.ofNat 64 p1
  e1 : S.regs 1 = BitVec.ofNat 64 l1
  e2 : S.regs 2 = BitVec.ofNat 64 c1
  r1 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z1 lm Z)
  l1b : l1 ≤ W lm
  ca : BC R L K g sp st zp zc M L1 zzp bp lm u pA cA
  lac : lA ≤ cA
  ca0 : 0 < cA
  s280 : M.readLE (sp + 280) 8 = pA
  s112 : M.readLE (sp + 112) 8 = lA
  s224 : M.readLE (sp + 224) 8 = cA
  hb : bodyB b s st lm sqC mlC i c + (SQ s st lm sqC + ML s st lm mlC + 2 * P2Pre.tC lm) ≤ b1 + cst

/-- after the second `sqr` (ra `1796352`): result `(p2, l2, c2)` (class `u`, `Z1²`); `Z1` in `(p1, l1, c1)` (class
`!u`, slots `440/232/120`) -/
structure J3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 p2 l2 c2 : Nat) :
    Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 1796352
  e0 : S.regs 0 = BitVec.ofNat 64 p2
  e1 : S.regs 1 = BitVec.ofNat 64 l2
  e2 : S.regs 2 = BitVec.ofNat 64 c2
  r2 : BC R L K g sp st zp zc M L1 zzp bp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z1 lm Z * Z1 lm Z)
  l2b : l2 ≤ 2 * W lm
  r1 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z1 lm Z)
  l1b : l1 ≤ W lm
  s440 : M.readLE (sp + 440) 8 = p1
  s232 : M.readLE (sp + 232) 8 = l1
  s120 : M.readLE (sp + 120) 8 = c1
  hb : bodyB b s st lm sqC mlC i c + (ML s st lm mlC + 2 * P2Pre.tC lm) ≤ b1 + cst

/-- after the second `trunc` (ra `1796372`): `(p2, l2, c2)` holds `Z2`, `l2 ≤ w` -/
structure J4 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 p2 l2 c2 : Nat) :
    Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 1796372
  e0 : S.regs 0 = BitVec.ofNat 64 p2
  e1 : S.regs 1 = BitVec.ofNat 64 l2
  e2 : S.regs 2 = BitVec.ofNat 64 c2
  r2 : BC R L K g sp st zp zc M L1 zzp bp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z2 lm Z)
  l2b : l2 ≤ W lm
  r1 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z1 lm Z)
  l1b : l1 ≤ W lm
  s440 : M.readLE (sp + 440) 8 = p1
  s232 : M.readLE (sp + 232) 8 = l1
  s120 : M.readLE (sp + 120) 8 = c1
  hb : bodyB b s st lm sqC mlC i c + (ML s st lm mlC + P2Pre.tC lm) ≤ b1 + cst

/-- after the `mul` (ra `1796460`): result `(p3, l3, c3)` (class `!u`, `Z2·powers[d]`); `Z2` in `(p2, l2, c2)`
(class `u`, slots `280/112/216`) -/
structure J5 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 p2 l2 c2 p3 l3 c3 : Nat) :
    Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 1796460
  e0 : S.regs 0 = BitVec.ofNat 64 p3
  e1 : S.regs 1 = BitVec.ofNat 64 l3
  e2 : S.regs 2 = BitVec.ofNat 64 c3
  r3 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) p3 c3
  n3 : NV M p3 l3 c3 (Z2 lm Z * Exp.p2Pow lm (natVal s.mem xp xl) (dOf yi))
  l3b : l3 ≤ 2 * W lm
  r2 : BC R L K g sp st zp zc M L1 zzp bp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z2 lm Z)
  l2b : l2 ≤ W lm
  s280 : M.readLE (sp + 280) 8 = p2
  s112 : M.readLE (sp + 112) 8 = l2
  s216 : M.readLE (sp + 216) 8 = c2
  hb : bodyB b s st lm sqC mlC i c + P2Pre.tC lm ≤ b1 + cst

/-- after the third `trunc` (ra `1796480`): `(p3, l3, c3)` holds `Z3 = stp Z d`, `l3 ≤ w` -/
structure J6 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 p2 l2 c2 p3 l3 c3 : Nat) :
    Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 1796480
  e0 : S.regs 0 = BitVec.ofNat 64 p3
  e1 : S.regs 1 = BitVec.ofNat 64 l3
  e2 : S.regs 2 = BitVec.ofNat 64 c3
  r3 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) p3 c3
  n3 : NV M p3 l3 c3 (Z3 lm (natVal s.mem xp xl) Z yi)
  l3b : l3 ≤ W lm
  r2 : BC R L K g sp st zp zc M L1 zzp bp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z2 lm Z)
  l2b : l2 ≤ W lm
  s280 : M.readLE (sp + 280) 8 = p2
  s112 : M.readLE (sp + 112) 8 = l2
  s216 : M.readLE (sp + 216) 8 = c2
  hb : bodyB b s st lm sqC mlC i c ≤ b1 + cst

/-- the continuation at join point `Jk` (all states, memories, live sets, budgets and buffers) -/
@[reducible] def KJ (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop)
    (J : State → Memory → List (Nat × Nat) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 a1 a2 a3 a4 a5 a6 : Nat), J S M L1 b1 a1 a2 a3 a4 a5 a6 →
    ReachesRet (LibW.program.link impl) ret0 S Q

end FvModexp.Arm64.P2W2
