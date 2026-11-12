import FvModexp.Proofs.Arm64.Exp.P2W4BMu
import FvModexp.Proofs.Arm64.Exp.P2W4BTr

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the loop body's join points `J1 … J10` (agent infra)

The body (nat.go:1084-1104, entered from the loop test with `c + 1` windows left, i.e. `k = c`) makes ten calls:
four times `zz = zz.sqr(z)` + `trunc` (returns `0x1b605c/0x1b6070`, `0x1b609c/0x1b60b0`, `0x1b60dc/0x1b60f0`,
`0x1b611c/0x1b6130`), then `zz = zz.mul(z, powers[yi >> 60])` (`0x1b6188`) + `trunc` (`0x1b619c`), swapping
`z`/`zz` after each product. Every join point is an instance of the generic `JX` (the common part `JC` + the
result `(pr, lr, cr)` in registers with class `v`, value `Vr`, `lr ≤ lrb` + the other live buffer `(po, lo, co)`
with class `w`, value `Vo`, `lo ≤ w`, spilled at `o1/o2/o3` + the budget `bodyB + rem ≤ b1 + cst`, `rem` = the
bound of the calls still to come). Values: `Zk+1 = Zk² mod 2^logM` (`k < 4`), `Z5 = Z4·powers[d] mod 2^logM =
stp Z d` (`d = yi >> 60`). Each segment `Bk` (one module each) proves `KJ(k+1) → KJk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

/-- the budget part common to the body: what the loop needs after this body -/
@[reducible] def bodyB (b : Nat) (s : State) (st lm : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c : Nat) : Nat :=
  b + (c + 16 * i) * bc sqC mlC (ℓL (stLen s.mem st) lm) lm + P2Pre.tC lm

/-- the `sqr` / `mul` bounds at the loop level -/
@[reducible] def SQ (s : State) (st lm : Nat) (sqC : Nat → Nat → Nat) : Nat := sqC (ℓL (stLen s.mem st) lm) (W lm)
@[reducible] def ML (s : State) (st lm : Nat) (mlC : Nat → Nat → Nat → Nat) : Nat :=
  mlC (ℓL (stLen s.mem st) lm) (W lm) (W lm)

/-- the window `d = yi >> 60` -/
@[reducible] def dOf (yi : Nat) : Nat := yi / 2 ^ 60

/-- the body's values -/
@[reducible] def Z1 (lm Z : Nat) : Nat := Z * Z % 2 ^ lm
@[reducible] def Z2 (lm Z : Nat) : Nat := Z1 lm Z * Z1 lm Z % 2 ^ lm
@[reducible] def Z3 (lm Z : Nat) : Nat := Z2 lm Z * Z2 lm Z % 2 ^ lm
@[reducible] def Z4 (lm Z : Nat) : Nat := Z3 lm Z * Z3 lm Z % 2 ^ lm
@[reducible] def Z5 (lm X Z yi : Nat) : Nat := Z4 lm Z * Exp.p2Pow lm X (dOf yi) % 2 ^ lm

theorem Z5_eq (lm X Z yi : Nat) : Z5 lm X Z yi = stp lm X Z (yi / 2 ^ (64 - 4)) := rfl

/-- the common facts at every join point of the body -/
structure JC (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
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
  hc : c < 16
  hu : u = true ↔ (c + 1 + kk) % 2 = 1
  hfv : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i yi (c + 1) Z = FV
  hcb : cst ≤ b

/-- `JC` through a step keeping the slots `[sp + 88, sp + 848)` (a callee) -/
theorem JC.call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm ret : Nat}
    {s : State} {r29 : BitVec 64} {zzp bp kk cst FV : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (h : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1)
    {S' : State} {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (esp : S'.sp = S.sp) (e28 : S'.regs 28 = S.regs 28) (e29 : S'.regs 29 = S.regs 29) (e18 : S'.regs 18 = S.regs 18)
    (em : S'.mem = M') (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M' L2 b2 zzp bp)
    (hk : ∀ a k, sp + 88 ≤ a → a + k ≤ sp + 848 → M'.readLE a k = M.readLE a k) :
    JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S' M' L2 b2 :=
  ⟨esp.trans h.esp, e28.trans h.e28, e29.trans h.e29, e18.trans h.e18, em, hB,
    (hk _ _ (by omega) (by omega)).trans h.s200, (hk _ _ (by omega) (by omega)).trans h.s208,
    (hk _ _ (by omega) (by omega)).trans h.s240, (hk _ _ (by omega) (by omega)).trans h.s160, h.hi, h.hyi, h.hc,
    h.hu, h.hfv, h.hcb⟩

/-- the own stores of the body: window slots off `ESl`, `200`, `208`, the result slots and the table headers -/
@[reducible] def SW (sp : Nat) (r : Nat × Nat) : Prop :=
  sp + 96 ≤ r.1 ∧ r.1 ≤ r.2 ∧ (r.2 ≤ sp + 200 ∨ (sp + 216 ≤ r.1 ∧ r.2 ≤ sp + 256) ∨
    (sp + 280 ≤ r.1 ∧ r.2 ≤ sp + 320) ∨ (sp + 728 ≤ r.1 ∧ r.2 ≤ sp + 736))

/-- `ESl` through stores that keep exactly the slots it reads -/
theorem ESl.keep2 {M1 M3 : Memory} {sp st : Nat} {r29 : BitVec 64} {ret zp zc xp xl xc yp yl lm len0 : Nat}
    (h : ESl M1 sp st r29 ret zp zc xp xl xc yp yl lm len0)
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 95 ≤ a ∧ a + k ≤ sp + 96 ∨ sp + 256 ≤ a ∧ a + k ≤ sp + 280 ∨
      sp + 704 ≤ a ∧ a + k ≤ sp + 728 ∨ sp + 736 ≤ a ∧ a + k ≤ sp + 744 ∨ sp + 760 ≤ a ∧ a + k ≤ sp + 848) →
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
    (∀ a k, (a + k ≤ sp + 96 ∨ sp + 848 ≤ a ∨ (sp + 200 ≤ a ∧ a + k ≤ sp + 216) ∨
      (sp + 256 ≤ a ∧ a + k ≤ sp + 280) ∨ (sp + 320 ≤ a ∧ a + k ≤ sp + 728) ∨ sp + 736 ≤ a) →
      M'.readLE a k = M.readLE a k) ∧
    (∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp bp lm w q d → 0 < d →
      BC R L K g sp st zp zc M' L1 zzp bp lm w q d ∧
        ∀ a k, q ≤ a → a + k ≤ q + 8 * d → M'.readLE a k = M.readLE a k) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 848) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a k, (a + k ≤ sp + 96 ∨ sp + 848 ≤ a ∨ (sp + 200 ≤ a ∧ a + k ≤ sp + 216) ∨
      (sp + 256 ≤ a ∧ a + k ≤ sp + 280) ∨ (sp + 320 ≤ a ∧ a + k ≤ sp + 728) ∨ sp + 736 ≤ a) →
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
    Exp.outerLoop 4 step y K i yi (c + 1) z =
      Exp.outerLoop 4 step y K i ((yi * 2 ^ 4) % Exp.B) c (step z (yi / 2 ^ (64 - 4))) := by
  cases i <;> rfl

/-! ## The join points (`Jk` at the return of call `k`; `KJk` = their continuations) -/

/-- the generic join point: at `pc`, the result `(pr, lr, cr)` in `R0..R2` (class `v`, value `Vr`, `lr ≤ lrb`), the
other live buffer `(po, lo, co)` (class `w`, value `Vo`, `lo ≤ w`, spilled at `sp + o1/o2/o3`), the calls still to
come bounded by `rem` -/
structure JX (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) (pc : Nat) (v w : Bool) (Vr lrb Vo o1 o2 o3 rem : Nat)
    (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 po lo co pr lr cr : Nat) : Prop where
  jc : JC R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u S M L1 b1
  epc : S.pc = BitVec.ofNat 64 pc
  e0 : S.regs 0 = BitVec.ofNat 64 pr
  e1 : S.regs 1 = BitVec.ofNat 64 lr
  e2 : S.regs 2 = BitVec.ofNat 64 cr
  rr : BC R L K g sp st zp zc M L1 zzp bp lm v pr cr
  nr : NV M pr lr cr Vr
  lrb : lr ≤ lrb
  ro : BC R L K g sp st zp zc M L1 zzp bp lm w po co
  no : NV M po lo co Vo
  lob : lo ≤ W lm
  so1 : M.readLE (sp + o1) 8 = po
  so2 : M.readLE (sp + o2) 8 = lo
  so3 : M.readLE (sp + o3) 8 = co
  hb : bodyB b s st lm sqC mlC i c + rem ≤ b1 + cst

/-- after `sqr` 1 (ra `0x1b605c`): `Z²` (class `!u`); other = `z` = `A` (class `u`, slots `280/112/224`) -/
@[reducible] def J1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794140 (!u) u (Z * Z) (2 * W lm) Z 280 112 224
    (3 * SQ s st lm sqC + ML s st lm mlC + 5 * P2Pre.tC lm)

/-- after `trunc` 1 (ra `0x1b6070`): `Z1` -/
@[reducible] def J2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794160 (!u) u (Z1 lm Z) (W lm) Z 280 112 224
    (3 * SQ s st lm sqC + ML s st lm mlC + 4 * P2Pre.tC lm)

/-- after `sqr` 2 (ra `0x1b609c`): `Z1²` (class `u`); other = `Z1` (class `!u`, slots `728/232/120`) -/
@[reducible] def J3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794204 u (!u) (Z1 lm Z * Z1 lm Z) (2 * W lm) (Z1 lm Z) 728 232 120
    (2 * SQ s st lm sqC + ML s st lm mlC + 4 * P2Pre.tC lm)

/-- after `trunc` 2 (ra `0x1b60b0`): `Z2` -/
@[reducible] def J4 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794224 u (!u) (Z2 lm Z) (W lm) (Z1 lm Z) 728 232 120
    (2 * SQ s st lm sqC + ML s st lm mlC + 3 * P2Pre.tC lm)

/-- after `sqr` 3 (ra `0x1b60dc`): `Z2²` (class `!u`); other = `Z2` (class `u`, slots `280/112/216`) -/
@[reducible] def J5 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794268 (!u) u (Z2 lm Z * Z2 lm Z) (2 * W lm) (Z2 lm Z) 280 112 216
    (SQ s st lm sqC + ML s st lm mlC + 3 * P2Pre.tC lm)

/-- after `trunc` 3 (ra `0x1b60f0`): `Z3` -/
@[reducible] def J6 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794288 (!u) u (Z3 lm Z) (W lm) (Z2 lm Z) 280 112 216
    (SQ s st lm sqC + ML s st lm mlC + 2 * P2Pre.tC lm)

/-- after `sqr` 4 (ra `0x1b611c`): `Z3²` (class `u`); other = `Z3` (class `!u`, slots `728/232/120`) -/
@[reducible] def J7 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794332 u (!u) (Z3 lm Z * Z3 lm Z) (2 * W lm) (Z3 lm Z) 728 232 120
    (ML s st lm mlC + 2 * P2Pre.tC lm)

/-- after `trunc` 4 (ra `0x1b6130`): `Z4` -/
@[reducible] def J8 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794352 u (!u) (Z4 lm Z) (W lm) (Z3 lm Z) 728 232 120
    (ML s st lm mlC + P2Pre.tC lm)

/-- after the `mul` (ra `0x1b6188`): `Z4·powers[d]` (class `!u`); other = `Z4` (class `u`, slots `280/112/216`) -/
@[reducible] def J9 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794440 (!u) u (Z4 lm Z * Exp.p2Pow lm (natVal s.mem xp xl) (dOf yi)) (2 * W lm) (Z4 lm Z) 280 112 216
    (P2Pre.tC lm)

/-- after `trunc` 5 (ra `0x1b619c`): `Z5 = stp Z d` -/
@[reducible] def J10 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat)
    (s : State) (r29 : BitVec 64) (zzp bp kk cst FV : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 zzp bp kk cst FV sqC mlC i c yi Z u
    1794460 (!u) u (Z5 lm (natVal s.mem xp xl) Z yi) (W lm) (Z4 lm Z) 280 112 216
    (0)

/-- the continuation at join point `Jk` (all states, memories, live sets, budgets and buffers) -/
@[reducible] def KJ (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop)
    (J : State → Memory → List (Nat × Nat) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 a1 a2 a3 a4 a5 a6 : Nat), J S M L1 b1 a1 a2 a3 a4 a5 a6 →
    ReachesRet (LibW.program.link impl) ret0 S Q

end FvModexp.Arm64.P2W4
