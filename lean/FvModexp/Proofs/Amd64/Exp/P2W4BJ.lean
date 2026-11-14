import FvModexp.Proofs.Amd64.Exp.P2W4BMu
import FvModexp.Proofs.Amd64.Exp.P2W4BTr
import FvModexp.Proofs.Amd64.Exp.P2W4LK

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the loop body's join points `J1 … J10` (agent divmc s77; amd64 twin of agent
infra's `Arm64.P2W4BJ`, built on the amd64 window-2 `P2W2BJ`)

The body (nat.go:1084-1104, entered from the loop test with `c + 1` windows left, i.e. `k = c`; amd64 fn+0x654 …)
makes ten calls: four times `zz = zz.sqr(z)` + `trunc` (returns +0x686/+0x69c, +0x6dc/+0x6f2, +0x732/+0x748,
+0x788/+0x79e), then `zz = zz.mul(z, powers[yi >> 60])` (+0x814) + `trunc` (+0x82a), swapping `z`/`zz` after each
product. Every join point is an instance of the generic `JX` (the common part `JC` + the result `(pr, lr, cr)` in
`AX, BX, CX` with class `v`, value `Vr`, `lr ≤ lrb` + the other live buffer `(po, lo, co)` with class `w`, value `Vo`,
`lo ≤ W`, spilled at `o1/o2/o3` + the budget `bodyB + rem ≤ b1 + cst`, `rem` = the bound of the calls still to come).
`JC`: RSP/R14/RBP/fsBase/X15/DF, `BF`, the slots `0xc8 = kk - 2`, `0xd0 = i`, `0xf0 = c`, `0x98 = yi`, bounds,
parity, model, `cst ≤ b`. Other-buffer slots: after calls 1/2 `z = (0x120, 0x68, 0xe0)`; 3/4 and 7/8
`(0x2e0, 0xe8, 0x70)`; 5/6 and 9/10 `(0x120, 0x68, 0xd8)`. Each segment `Bk` (one module each) proves `KJ(k+1) → KJk`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the budget part common to the body: what the loop needs after this body -/
@[reducible] def bodyB (b lm i c : Nat) : Nat := b + (c + 16 * i) * bc lm + P2Pre.tC lm

/-- the window `d = yi >> 60` -/
@[reducible] def dOf (yi : Nat) : Nat := yi / 2 ^ 60

/-- the body's values -/
@[reducible] def Z1 (lm Z : Nat) : Nat := Z * Z % 2 ^ lm
@[reducible] def Z2 (lm Z : Nat) : Nat := Z1 lm Z * Z1 lm Z % 2 ^ lm
@[reducible] def Z3 (lm Z : Nat) : Nat := Z2 lm Z * Z2 lm Z % 2 ^ lm
@[reducible] def Z4 (lm Z : Nat) : Nat := Z3 lm Z * Z3 lm Z % 2 ^ lm
@[reducible] def Z5 (lm X Z yi : Nat) : Nat := Z4 lm Z * Exp.p2Pow lm X (dOf yi) % 2 ^ lm

theorem Z5_eq (lm X Z yi : Nat) : Z5 lm X Z yi = stp lm X Z (yi / 2 ^ (64 - 4)) := rfl

theorem bud_c1 (X c i : Nat) : (c + 1 + 16 * i) * X = (c + 16 * i) * X + X := by
  rw [show c + 1 + 16 * i = (c + 16 * i) + 1 by omega, Nat.succ_mul]

theorem sub1c (i : Nat) : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem outer_succ (step : Nat → Nat → Nat) (y K i yi c z : Nat) :
    Exp.outerLoop 4 step y K i yi (c + 1) z =
      Exp.outerLoop 4 step y K i ((yi * 2 ^ 4) % Exp.B) c (step z (yi / 2 ^ (64 - 4))) := by
  cases i <;> rfl

/-- the common facts at every join point of the body -/
structure JC (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  esp : S.regs 4 = BitVec.ofNat 64 sp
  e14 : S.regs 14 = BitVec.ofNat 64 g
  e5 : S.regs 5 = r5
  efs : S.fsBase = s.fsBase
  ex : S.xmm 15 = 0
  edf : S.df = false
  em : S.mem = M
  bf : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp
  sc0 : M.readLE (sp + 0xc8) 8 = (BitVec.ofNat 64 kk - 2#64).toNat
  sc8 : M.readLE (sp + 0xd0) 8 = i
  sf0 : M.readLE (sp + 0xf0) 8 = c
  s98 : M.readLE (sp + 0x98) 8 = yi
  hi : i < yl
  hyi : yi < 2 ^ 64
  hc : c < 16
  hu : u = true ↔ (c + 1 + kk) % 2 = 1
  hfv : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i yi (c + 1) Z = FV
  hcb : cst ≤ b

/-- the body's own window stores: below `sp + 0x2e8`, off the `ESl` slots, `0xc0`/`0xc8` and the table headers -/
@[reducible] def SW (sp : Nat) (q : Nat × Nat) : Prop :=
  sp ≤ q.1 ∧ q.1 ≤ q.2 ∧ (q.2 ≤ sp + 0x57 ∨ (sp + 0x58 ≤ q.1 ∧ q.2 ≤ sp + 0xc8) ∨
    (sp + 0xd8 ≤ q.1 ∧ q.2 ≤ sp + 0x108) ∨ (sp + 0x120 ≤ q.1 ∧ q.2 ≤ sp + 0x148) ∨
    (sp + 0x2e0 ≤ q.1 ∧ q.2 ≤ sp + 0x2e8))

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `BF` and every buffer (class, bytes) through the body's own window stores (`SW`) -/
theorem BF.win (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ q ∈ ws, SW sp q) :
    BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M' L1 b1 zzp tp ∧
    (∀ a k, (a + k ≤ sp ∨ sp + 0x2e8 ≤ a ∨ (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58) ∨
      (sp + 0xc8 ≤ a ∧ a + k ≤ sp + 0xd8) ∨ (sp + 0x108 ≤ a ∧ a + k ≤ sp + 0x120) ∨
      (sp + 0x148 ≤ a ∧ a + k ≤ sp + 0x2e0)) → M'.readLE a k = M.readLE a k) ∧
    (∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp tp lm w q d → 0 < d →
      BC R L K g sp st zp zc M' L1 zzp tp lm w q d ∧
        ∀ a k, q ≤ a → a + k ≤ q + 8 * d → M'.readLE a k = M.readLE a k) := by
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hstw : Apart st 24 (sp - 0x8 - K) (K + 0x360) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a k, (a + k ≤ sp ∨ sp + 0x2e8 ≤ a ∨ (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58) ∨
      (sp + 0xc8 ≤ a ∧ a + k ≤ sp + 0xd8) ∨ (sp + 0x108 ≤ a ∧ a + k ≤ sp + 0x120) ∨
      (sp + 0x148 ≤ a ∧ a + k ≤ sp + 0x2e0)) → M'.readLE a k = M.readLE a k := fun a k ha =>
    hF.readLE a k (outside_of_forall fun q hq => by have := hws q hq; simp only [SW] at this; omega)
  have hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w := hF.accessible
  have e0 : stW M' st = stW M st := hrd _ _ (by omega)
  have e1 : stLen M' st = stLen M st := hrd _ _ (by omega)
  have e2 : stCap M' st = stCap M st := hrd _ _ (by omega)
  have hbW := scr_win hP hB.tz.bscr
  unfold Apart at hbW
  refine ⟨⟨WC.win hP hB.wc hF hrg (fun q hq => by have := hws q hq; simp only [SW, InWN] at this ⊢; omega),
    ESl.keep hB.esl (fun a k ha => hrd a k (by omega)),
    hB.tz.keep hacc (LiveExt.refl R L1) e0 e1 e2 (fun a k ha => hrd a k (by omega))⟩, hrd, fun w q d hq hd => ?_⟩
  have hqW := (BC.facts hP hB hq hd).2.2.1
  unfold Apart at hqW
  refine ⟨?_, fun a k h1 h2 => hrd a k (by omega)⟩
  cases w
  · exact hq
  · exact UB.keep hq hacc (LiveExt.refl R L1) e0 e1 e2

end

/-- `JC` through a step keeping the slots `[sp + 0x50, sp + 0x358)` (a callee) -/
theorem JC.call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st bp r zp zc xp xl xc yp yl lm : Nat}
    {s : State} {r5 : W64} {zzp tp kk cst FV : Nat} {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat}
    (h : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1)
    {S' : State} {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (esp : S'.regs 4 = S.regs 4) (e14 : S'.regs 14 = S.regs 14) (e5 : S'.regs 5 = S.regs 5)
    (efs : S'.fsBase = s.fsBase) (ex : S'.xmm 15 = 0) (edf : S'.df = false)
    (em : S'.mem = M') (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M' L2 b2 zzp tp)
    (hk : ∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x358 → M'.readLE a k = M.readLE a k) :
    JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S' M' L2 b2 :=
  ⟨esp.trans h.esp, e14.trans h.e14, e5.trans h.e5, efs, ex, edf, em, hB,
    (hk _ _ (by omega) (by omega)).trans h.sc0, (hk _ _ (by omega) (by omega)).trans h.sc8,
    (hk _ _ (by omega) (by omega)).trans h.sf0, (hk _ _ (by omega) (by omega)).trans h.s98, h.hi, h.hyi, h.hc,
    h.hu, h.hfv, h.hcb⟩

/-! ## The join points (`Jk` at the return of call `k`; `KJk` = their continuations) -/

/-- the generic join point at `pc`: result `(pr, lr, cr)` in `AX, BX, CX` (class `v`, value `Vr`, `lr ≤ lrb`), the
other buffer `(po, lo, co)` (class `w`, value `Vo`, `lo ≤ W`) spilled at `o1/o2/o3`, and `rem` budget left -/
structure JX (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool)
    (pc : Nat) (v w : Bool) (Vr lrb Vo o1 o2 o3 rem : Nat)
    (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 po lo co pr lr cr : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 pc
  e0 : S.regs 0 = BitVec.ofNat 64 pr
  e3 : S.regs 3 = BitVec.ofNat 64 lr
  e1 : S.regs 1 = BitVec.ofNat 64 cr
  rr : BC R L K g sp st zp zc M L1 zzp tp lm v pr cr
  nr : NV M pr lr cr Vr
  lrb : lr ≤ lrb
  ro : BC R L K g sp st zp zc M L1 zzp tp lm w po co
  no : NV M po lo co Vo
  lob : lo ≤ W lm
  so1 : M.readLE (sp + o1) 8 = po
  so2 : M.readLE (sp + o2) 8 = lo
  so3 : M.readLE (sp + o3) 8 = co
  hb : bodyB b lm i c + rem ≤ b1 + cst

/-- after `sqr` 1 (ra fn+0x686): `Z²` (class `!u`); other = `z` = `A` (class `u`, slots `0x120/0x68/0xe0`) -/
@[reducible] def J1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199622 (!u) u (Z * Z) (2 * W lm) Z 0x120 0x68 0xe0
    (3 * sqrCQ (W lm) + mulCQ (W lm) (W lm) + 5 * P2Pre.tC lm)

/-- after `trunc` 1 (ra fn+0x69c): `Z1` -/
@[reducible] def J2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199644 (!u) u (Z1 lm Z) (W lm) Z 0x120 0x68 0xe0
    (3 * sqrCQ (W lm) + mulCQ (W lm) (W lm) + 4 * P2Pre.tC lm)

/-- after `sqr` 2 (ra fn+0x6dc): `Z1²` (class `u`); other = `Z1` (class `!u`, slots `0x2e0/0xe8/0x70`) -/
@[reducible] def J3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199708 u (!u) (Z1 lm Z * Z1 lm Z) (2 * W lm) (Z1 lm Z) 0x2e0 0xe8 0x70
    (2 * sqrCQ (W lm) + mulCQ (W lm) (W lm) + 4 * P2Pre.tC lm)

/-- after `trunc` 2 (ra fn+0x6f2): `Z2` -/
@[reducible] def J4 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199730 u (!u) (Z2 lm Z) (W lm) (Z1 lm Z) 0x2e0 0xe8 0x70
    (2 * sqrCQ (W lm) + mulCQ (W lm) (W lm) + 3 * P2Pre.tC lm)

/-- after `sqr` 3 (ra fn+0x732): `Z2²` (class `!u`); other = `Z2` (class `u`, slots `0x120/0x68/0xd8`) -/
@[reducible] def J5 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199794 (!u) u (Z2 lm Z * Z2 lm Z) (2 * W lm) (Z2 lm Z) 0x120 0x68 0xd8
    (sqrCQ (W lm) + mulCQ (W lm) (W lm) + 3 * P2Pre.tC lm)

/-- after `trunc` 3 (ra fn+0x748): `Z3` -/
@[reducible] def J6 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199816 (!u) u (Z3 lm Z) (W lm) (Z2 lm Z) 0x120 0x68 0xd8
    (sqrCQ (W lm) + mulCQ (W lm) (W lm) + 2 * P2Pre.tC lm)

/-- after `sqr` 4 (ra fn+0x788): `Z3²` (class `u`); other = `Z3` (class `!u`, slots `0x2e0/0xe8/0x70`) -/
@[reducible] def J7 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199880 u (!u) (Z3 lm Z * Z3 lm Z) (2 * W lm) (Z3 lm Z) 0x2e0 0xe8 0x70
    (mulCQ (W lm) (W lm) + 2 * P2Pre.tC lm)

/-- after `trunc` 4 (ra fn+0x79e): `Z4` -/
@[reducible] def J8 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6199902 u (!u) (Z4 lm Z) (W lm) (Z3 lm Z) 0x2e0 0xe8 0x70
    (mulCQ (W lm) (W lm) + P2Pre.tC lm)

/-- after the `mul` (ra fn+0x814): `Z4·powers[d]` (class `!u`); other = `Z4` (class `u`, slots `0x120/0x68/0xd8`) -/
@[reducible] def J9 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6200020 (!u) u (Z4 lm Z * Exp.p2Pow lm (natVal s.mem xp xl) (dOf yi)) (2 * W lm) (Z4 lm Z) 0x120 0x68 0xd8
    (P2Pre.tC lm)

/-- after `trunc` 5 (ra fn+0x82a): `Z5 = stp Z d` -/
@[reducible] def J10 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat)
    (s : State) (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) :=
  JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
    6200042 (!u) u (Z5 lm (natVal s.mem xp xl) Z yi) (W lm) (Z4 lm Z) 0x120 0x68 0xd8
    (0)

/-- the continuation at join point `Jk` (all states, memories, live sets, budgets and buffers) -/
@[reducible] def KJ (impl : List Amd64.Segment) (ret0 : W64) (Q : State → Prop)
    (J : State → Memory → List (Nat × Nat) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 a1 a2 a3 a4 a5 a6 : Nat), J S M L1 b1 a1 a2 a3 a4 a5 a6 →
    ReachesRet (LibW.program.link impl) ret0 S Q

end FvModexp.Amd64.P2W4
