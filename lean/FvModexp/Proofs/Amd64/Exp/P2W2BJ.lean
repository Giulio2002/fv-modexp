import FvModexp.Proofs.Amd64.Exp.P2W2BMu
import FvModexp.Proofs.Amd64.Exp.P2W2BTr
import FvModexp.Proofs.Amd64.Exp.P2W2LK

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop body's join points `J1 … J6` (agent divmc s73; amd64 twin of agent
infra's `Arm64.P2W2BJ`)

The body (nat.go:1235-1247, entered from the loop test with `c + 1` windows left, i.e. `k = c`; amd64 fn+0x645 …)
makes six calls: `zz = zz.sqr(z)` (return fn+0x677), `trunc` (+0x68d), `z = z.sqr(zz)` (+0x6cd), `trunc` (+0x6e5),
`zz = zz.mul(z, powers[yi >> 62])` (+0x75b), `trunc` (+0x771).
`Jk` = the facts at the return of call `k`: the common part `JC` (RSP/R14/RBP/fsBase/X15/DF, `BF`, the slots
`0xc0 = kk - 2`, `0xc8 = i`, `0xf0 = c`, `0x98 = yi`, bounds, parity, model, `cst ≤ b`) plus the two live buffers
with classes, values, result registers `AX, BX, CX` and the budget `bodyB + rk ≤ b1 + cst` (`rk` = the bound of the
calls still to come). Slots: after call 1/2 `z = (0x118, 0x68, 0xe0)`; after 3/4 `Z1 = (0x1b8, 0xd8, 0x70)`; after
5/6 `Z2 = (0x118, 0x68, 0xd0)`. Each segment `Bk` (one module each) proves `KJ(k+1) → KJk`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the budget part common to the body: what the loop needs after this body -/
@[reducible] def bodyB (b lm i c : Nat) : Nat := b + (c + 32 * i) * bc lm + P2Pre.tC lm

/-- the window `d = yi >> 62` -/
@[reducible] def dOf (yi : Nat) : Nat := yi / 2 ^ 62

/-- the body's values -/
@[reducible] def Z1 (lm Z : Nat) : Nat := Z * Z % 2 ^ lm
@[reducible] def Z2 (lm Z : Nat) : Nat := Z1 lm Z * Z1 lm Z % 2 ^ lm
@[reducible] def Z3 (lm X Z yi : Nat) : Nat := Z2 lm Z * Exp.p2Pow lm X (dOf yi) % 2 ^ lm

theorem Z3_eq (lm X Z yi : Nat) : Z3 lm X Z yi = stp lm X Z (yi / 2 ^ (64 - 2)) := rfl

theorem bud_c1 (X c i : Nat) : (c + 1 + 32 * i) * X = (c + 32 * i) * X + X := by
  rw [show c + 1 + 32 * i = (c + 32 * i) + 1 by omega, Nat.succ_mul]

theorem sub1c (i : Nat) : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem outer_succ (step : Nat → Nat → Nat) (y K i yi c z : Nat) :
    Exp.outerLoop 2 step y K i yi (c + 1) z =
      Exp.outerLoop 2 step y K i ((yi * 2 ^ 2) % Exp.B) c (step z (yi / 2 ^ (64 - 2))) := by
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
  sc0 : M.readLE (sp + 0xc0) 8 = (BitVec.ofNat 64 kk - 2#64).toNat
  sc8 : M.readLE (sp + 0xc8) 8 = i
  sf0 : M.readLE (sp + 0xf0) 8 = c
  s98 : M.readLE (sp + 0x98) 8 = yi
  hi : i < yl
  hyi : yi < 2 ^ 64
  hc : c < 32
  hu : u = true ↔ (c + 1 + kk) % 2 = 1
  hfv : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i yi (c + 1) Z = FV
  hcb : cst ≤ b

/-- the body's own window stores: below `sp + 0x1c0`, off the `ESl` slots, `0xc0`/`0xc8` and the table headers -/
@[reducible] def SW (sp : Nat) (q : Nat × Nat) : Prop :=
  sp ≤ q.1 ∧ q.1 ≤ q.2 ∧ (q.2 ≤ sp + 0x57 ∨ (sp + 0x58 ≤ q.1 ∧ q.2 ≤ sp + 0xc0) ∨
    (sp + 0xd0 ≤ q.1 ∧ q.2 ≤ sp + 0x100) ∨ (sp + 0x118 ≤ q.1 ∧ q.2 ≤ sp + 0x140) ∨
    (sp + 0x1b8 ≤ q.1 ∧ q.2 ≤ sp + 0x1c0))

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `BF` and every buffer (class, bytes) through the body's own window stores (`SW`) -/
theorem BF.win (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ q ∈ ws, SW sp q) :
    BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M' L1 b1 zzp tp ∧
    (∀ a k, (a + k ≤ sp ∨ sp + 0x1c0 ≤ a ∨ (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58) ∨
      (sp + 0xc0 ≤ a ∧ a + k ≤ sp + 0xd0) ∨ (sp + 0x100 ≤ a ∧ a + k ≤ sp + 0x118) ∨
      (sp + 0x140 ≤ a ∧ a + k ≤ sp + 0x1b8)) → M'.readLE a k = M.readLE a k) ∧
    (∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp tp lm w q d → 0 < d →
      BC R L K g sp st zp zc M' L1 zzp tp lm w q d ∧
        ∀ a k, q ≤ a → a + k ≤ q + 8 * d → M'.readLE a k = M.readLE a k) := by
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hstw : Apart st 24 (sp - 8 - K) (K + 0x238) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a k, (a + k ≤ sp ∨ sp + 0x1c0 ≤ a ∨ (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58) ∨
      (sp + 0xc0 ≤ a ∧ a + k ≤ sp + 0xd0) ∨ (sp + 0x100 ≤ a ∧ a + k ≤ sp + 0x118) ∨
      (sp + 0x140 ≤ a ∧ a + k ≤ sp + 0x1b8)) → M'.readLE a k = M.readLE a k := fun a k ha =>
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

/-- `JC` through a step keeping the slots `[sp + 0x50, sp + 0x230)` (a callee) -/
theorem JC.call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st bp r zp zc xp xl xc yp yl lm : Nat}
    {s : State} {r5 : W64} {zzp tp kk cst FV : Nat} {i c yi Z : Nat} {u : Bool} {S : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat}
    (h : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1)
    {S' : State} {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (esp : S'.regs 4 = S.regs 4) (e14 : S'.regs 14 = S.regs 14) (e5 : S'.regs 5 = S.regs 5)
    (efs : S'.fsBase = s.fsBase) (ex : S'.xmm 15 = 0) (edf : S'.df = false)
    (em : S'.mem = M') (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M' L2 b2 zzp tp)
    (hk : ∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x230 → M'.readLE a k = M.readLE a k) :
    JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S' M' L2 b2 :=
  ⟨esp.trans h.esp, e14.trans h.e14, e5.trans h.e5, efs, ex, edf, em, hB,
    (hk _ _ (by omega) (by omega)).trans h.sc0, (hk _ _ (by omega) (by omega)).trans h.sc8,
    (hk _ _ (by omega) (by omega)).trans h.sf0, (hk _ _ (by omega) (by omega)).trans h.s98, h.hi, h.hyi, h.hc,
    h.hu, h.hfv, h.hcb⟩

/-! ## The join points (`Jk` at the return of call `k`; `KJk` = their continuations) -/

/-- after `zz = zz.sqr(z)` (ra fn+0x677): result `(p1, l1, c1)` (class `!u`, `Z²`); `A = (pA, lA, cA)` (class `u`,
slots `0x118/0x68/0xe0`) -/
structure J1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 pA lA cA p1 l1 c1 : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 6202519
  e0 : S.regs 0 = BitVec.ofNat 64 p1
  e3 : S.regs 3 = BitVec.ofNat 64 l1
  e1 : S.regs 1 = BitVec.ofNat 64 c1
  r1 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z * Z)
  l1b : l1 ≤ 2 * W lm
  ca : BC R L K g sp st zp zc M L1 zzp tp lm u pA cA
  na : NV M pA lA cA Z
  la : lA ≤ W lm
  s118 : M.readLE (sp + 0x118) 8 = pA
  s68 : M.readLE (sp + 0x68) 8 = lA
  se0 : M.readLE (sp + 0xe0) 8 = cA
  hb : bodyB b lm i c + (sqrCQ (W lm) + mulCQ (W lm) (W lm) + 3 * P2Pre.tC lm) ≤ b1 + cst

/-- after the first `trunc` (ra fn+0x68d): `(p1, l1, c1)` holds `Z1`, `l1 ≤ w` -/
structure J2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 pA lA cA p1 l1 c1 : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 6202541
  e0 : S.regs 0 = BitVec.ofNat 64 p1
  e3 : S.regs 3 = BitVec.ofNat 64 l1
  e1 : S.regs 1 = BitVec.ofNat 64 c1
  r1 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z1 lm Z)
  l1b : l1 ≤ W lm
  ca : BC R L K g sp st zp zc M L1 zzp tp lm u pA cA
  na : NV M pA lA cA Z
  la : lA ≤ W lm
  s118 : M.readLE (sp + 0x118) 8 = pA
  s68 : M.readLE (sp + 0x68) 8 = lA
  se0 : M.readLE (sp + 0xe0) 8 = cA
  hb : bodyB b lm i c + (sqrCQ (W lm) + mulCQ (W lm) (W lm) + 2 * P2Pre.tC lm) ≤ b1 + cst

/-- after `z = z.sqr(zz)` (ra fn+0x6cd): result `(p2, l2, c2)` (class `u`, `Z1²`); `Z1` in `(p1, l1, c1)` (class
`!u`, slots `0x1b8/0xd8/0x70`) -/
structure J3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 p1 l1 c1 p2 l2 c2 : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 6202605
  e0 : S.regs 0 = BitVec.ofNat 64 p2
  e3 : S.regs 3 = BitVec.ofNat 64 l2
  e1 : S.regs 1 = BitVec.ofNat 64 c2
  r2 : BC R L K g sp st zp zc M L1 zzp tp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z1 lm Z * Z1 lm Z)
  l2b : l2 ≤ 2 * W lm
  r1 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z1 lm Z)
  l1b : l1 ≤ W lm
  s1b8 : M.readLE (sp + 0x1b8) 8 = p1
  sd8 : M.readLE (sp + 0xd8) 8 = l1
  s70 : M.readLE (sp + 0x70) 8 = c1
  hb : bodyB b lm i c + (mulCQ (W lm) (W lm) + 2 * P2Pre.tC lm) ≤ b1 + cst

/-- after the second `trunc` (ra fn+0x6e5): `(p2, l2, c2)` holds `Z2`, `l2 ≤ w` -/
structure J4 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 p1 l1 c1 p2 l2 c2 : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 6202629
  e0 : S.regs 0 = BitVec.ofNat 64 p2
  e3 : S.regs 3 = BitVec.ofNat 64 l2
  e1 : S.regs 1 = BitVec.ofNat 64 c2
  r2 : BC R L K g sp st zp zc M L1 zzp tp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z2 lm Z)
  l2b : l2 ≤ W lm
  r1 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) p1 c1
  n1 : NV M p1 l1 c1 (Z1 lm Z)
  l1b : l1 ≤ W lm
  s1b8 : M.readLE (sp + 0x1b8) 8 = p1
  sd8 : M.readLE (sp + 0xd8) 8 = l1
  s70 : M.readLE (sp + 0x70) 8 = c1
  hb : bodyB b lm i c + (mulCQ (W lm) (W lm) + P2Pre.tC lm) ≤ b1 + cst

/-- after the `mul` (ra fn+0x75b): result `(p3, l3, c3)` (class `!u`, `Z2·powers[d]`); `Z2` in `(p2, l2, c2)` (class
`u`, slots `0x118/0x68/0xd0`) -/
structure J5 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 p2 l2 c2 p3 l3 c3 : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 6202747
  e0 : S.regs 0 = BitVec.ofNat 64 p3
  e3 : S.regs 3 = BitVec.ofNat 64 l3
  e1 : S.regs 1 = BitVec.ofNat 64 c3
  r3 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) p3 c3
  n3 : NV M p3 l3 c3 (Z2 lm Z * Exp.p2Pow lm (natVal s.mem xp xl) (dOf yi))
  l3b : l3 ≤ 2 * W lm
  r2 : BC R L K g sp st zp zc M L1 zzp tp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z2 lm Z)
  l2b : l2 ≤ W lm
  s118 : M.readLE (sp + 0x118) 8 = p2
  s68 : M.readLE (sp + 0x68) 8 = l2
  sd0 : M.readLE (sp + 0xd0) 8 = c2
  hb : bodyB b lm i c + P2Pre.tC lm ≤ b1 + cst

/-- after the third `trunc` (ra fn+0x771): `(p3, l3, c3)` holds `Z3 = stp Z d`, `l3 ≤ w` -/
structure J6 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat) (i c yi Z : Nat) (u : Bool) (S : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 p2 l2 c2 p3 l3 c3 : Nat) : Prop where
  jc : JC R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1
  epc : S.rip = BitVec.ofNat 64 6202769
  e0 : S.regs 0 = BitVec.ofNat 64 p3
  e3 : S.regs 3 = BitVec.ofNat 64 l3
  e1 : S.regs 1 = BitVec.ofNat 64 c3
  r3 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) p3 c3
  n3 : NV M p3 l3 c3 (Z3 lm (natVal s.mem xp xl) Z yi)
  l3b : l3 ≤ W lm
  r2 : BC R L K g sp st zp zc M L1 zzp tp lm u p2 c2
  n2 : NV M p2 l2 c2 (Z2 lm Z)
  l2b : l2 ≤ W lm
  s118 : M.readLE (sp + 0x118) 8 = p2
  s68 : M.readLE (sp + 0x68) 8 = l2
  sd0 : M.readLE (sp + 0xd0) 8 = c2
  hb : bodyB b lm i c ≤ b1 + cst

/-- the continuation at join point `Jk` (all states, memories, live sets, budgets and buffers) -/
@[reducible] def KJ (impl : List Amd64.Segment) (ret0 : W64) (Q : State → Prop)
    (J : State → Memory → List (Nat × Nat) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 a1 a2 a3 a4 a5 a6 : Nat), J S M L1 b1 a1 a2 a3 a4 a5 a6 →
    ReachesRet (LibW.program.link impl) ret0 S Q

end FvModexp.Amd64.P2W2
