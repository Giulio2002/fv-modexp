import FvModexp.Proofs.Arm64.Exp.EvLN
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join points after the entry (agent infra)

`JX` = the facts common to every join point (`sp`, `g`, FP, `X18`, the context `WC` at level `ℓ`, the slots `ESl`,
the remaining budget `rk ≤ b1`). `Jk` = `JX` + the live locals at the return of call `k` (pc, result registers).
`LN.rd` / `DL.wr`: a local as a callee's input (`RdIn`) / destination (`WrOut`) at `SP = sp`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- `n = tz(m)` -/
@[reducible] def nE (s : State) (mp ml : Nat) : Nat := Exp.tz (natVal s.mem mp ml)

/-- the facts common to every join point -/
structure JX (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (S : State) (L1 : List (Nat × Nat)) (b1 ℓ rk : Nat) : Prop where
  esp : S.sp = BitVec.ofNat 64 sp
  e28 : S.regs 28 = BitVec.ofNat 64 g
  e29 : S.regs 29 = BitVec.ofNat 64 (sp - 8)
  e18 : S.regs 18 = s.regs 18
  wc : WC R L K g sp st zp zc s.mem S.mem L1 b1 ℓ
  esl : ESl S.mem sp st (s.regs 29) ret zp zc xp xl xc yp yl yc mp ml mc (stLen s.mem st) (nE s mp ml)
  bud : rk ≤ b1

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a live local (`0 < c`) as a callee input at `SP = sp` -/
theorem LN.rd (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory} {L1 : List (Nat × Nat)}
    {p l c v : Nat} (h : LN R L s.mem st M L1 p l c v) (hc : 0 < c) {S : State} (hsp : S.sp.toNat = sp)
    (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 128) :
    ExpHyp.RdIn R L1 S stk above p l := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨c40, hlv, hlo⟩, hlc, -, -⟩ := h
  obtain ⟨-, a2, a3, a4⟩ := hlv hc
  obtain ⟨w1, -⟩ := Loc.ap hP (hlo hc).1
  unfold Apart at w1
  subst hm
  refine ⟨by omega, Memory.accessible_weaken _ (Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega)), by omega,
    a2.sub (by omega) (by omega), ?_⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- a destination as a callee's output array at `SP = sp` -/
theorem DL.wr (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory} {L1 : List (Nat × Nat)}
    {p c : Nat} (h : DL R L s.mem st M L1 p c) {S : State} (hsp : S.sp.toNat = sp) (h28 : (S.regs 28).toNat = g)
    (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 128) :
    ExpHyp.WrOut R L1 S stk above p c := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨c40, hlv, hlo⟩ := h
  subst hm
  refine ⟨c40, hlv, fun hc => ?_⟩
  obtain ⟨w1, -, w3, -⟩ := Loc.ap hP (hlo hc).1
  unfold Apart at w1
  refine ⟨?_, by rw [h28]; exact w3⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

end

/-- a located array (`0 < k`) is apart from a range held at the entry and apart from the entry free part -/
theorem Loc.apart {R : RtInv} {L : List (Nat × Nat)} {m0 : Memory} {st t k a n : Nat} (h : Loc R L m0 st t k)
    (hk : 0 < k) (hh : Held R L a n)
    (hf : stLen m0 st < stCap m0 st → Apart a n (stW m0 st + 8 * stLen m0 st) (8 * (stCap m0 st - stLen m0 st))) :
    Apart t (8 * k) a n := by
  rcases h with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · have := hf (by omega); unfold Apart at this ⊢; omega
  · exact hfresh hh hap hin

/-- `JX` through a callee step (registers kept, the new context, the slots kept) -/
theorem JX.call {R : RtInv} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s S : State} {L1 : List (Nat × Nat)} {b1 ℓ rk : Nat}
    (h : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 ℓ rk) {S' : State}
    {L2 : List (Nat × Nat)} {b2 rk' : Nat}
    (esp : S'.sp = S.sp) (e28 : S'.regs 28 = S.regs 28) (e29 : S'.regs 29 = S.regs 29) (e18 : S'.regs 18 = S.regs 18)
    (hw : WC R L K g sp st zp zc s.mem S'.mem L2 b2 ℓ)
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 128 ≤ a ∧ a + k ≤ sp + 448) → S'.mem.readLE a k = S.mem.readLE a k)
    (hsp8 : 8 ≤ sp) (hb : rk' ≤ b2) : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S' L2 b2 ℓ rk' :=
  ⟨esp.trans h.esp, e28.trans h.e28, e29.trans h.e29, e18.trans h.e18, hw,
    h.esl.keep (fun a k ha => hk a k (by simp only [SlotR] at ha; omega)) hsp8, hb⟩

/-- a range apart from `[b, b + k)` is outside it -/
theorem out1_of_apart {a n b k : Nat} (h : Apart b k a n) : Outside a n [(b, b + k)] := by
  unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the stack header is outside a callee window at `SP = sp` -/
theorem EPre.st_cw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 128) : Outside st 24 [(sp - stk, sp - 8), (sp + 8, sp + above)] := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  simp only [outside_cons, outside_nil, and_true]; omega

/-- a store range of the function's own frame -/
@[reducible] def OwnR (sp K : Nat) (r : Nat × Nat) : Prop :=
  r.1 ≤ r.2 ∧ (sp - K ≤ r.1 ∧ r.2 ≤ sp + 328 ∨ sp + 344 ≤ r.1 ∧ r.2 ≤ sp + 448)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `WC` and every live local through the function's own stores -/
theorem WC.own (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory}
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions) (hws : ∀ r ∈ ws, OwnR sp K r) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ ∧
      ∀ q l c v, LN R L s.mem st M L1 q l c v → LN R L s.mem st M' L1 q l c v := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hLs : LiveSep L [(sp - K, sp + 448)] := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hwin : ∀ a k, (a + k ≤ sp - K ∨ sp + 448 ≤ a) → Outside a k ws := by
    intro a k ha
    refine outside_of_forall ?_
    intro r hr; have := hws r hr; omega
  refine ⟨h.frame hF hrg (fun a k ho => ?_) (fun a k hin _ => ?_) (hwin _ _ (by omega)) (fun r hr => ?_), ?_⟩
  · refine outside_of_forall fun r hr => ?_
    have := hws r hr
    simp only [WN, outside_append, outside_cons, outside_nil, and_true] at ho
    omega
  · obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this
    exact hwin _ _ (by omega)
  · right
    have := hws r hr
    exact hout.of_sub (by omega) (by omega)
  · intro q l c v hq
    refine hq.keep (LiveExt.refl R L1) hF.accessible (fun c0 a k h1 h2 => hF.readLE a k (hwin a k ?_))
      (fun c0 => (hq.1.2.2 c0).2.mono (LiveExt.refl R L1) ?_ ?_)
    · obtain ⟨w1, -⟩ := Loc.ap hP (hq.1.2.2 c0).1; unfold Apart at w1; omega
    · show M.readLE (st + 8) 8 ≤ M'.readLE (st + 8) 8
      rw [hF.readLE _ _ (hwin _ _ (by omega))]; exact Nat.le_refl _
    · left
      exact ⟨hF.readLE _ _ (hwin _ _ (by omega)), hF.readLE _ _ (hwin _ _ (by omega))⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

/-- `n = tz M ∈ [1, 64 ml)` for an even positive `M` -/
theorem nE_bd (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) : 0 < nE s mp ml ∧ nE s mp ml < 64 * ml := by
  have hlt : natVal s.mem mp ml < 2 ^ (64 * ml) := by
    have := Memory.readLE_lt s.mem mp (8 * ml)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * ml) = 64 * ml by omega] at this
    exact this
  refine ⟨?_, tz_lt hM hlt⟩
  show 0 < Exp.tz (natVal s.mem mp ml)
  rw [Exp.tz_even (by omega) hev]; omega

end

/-- budget steps, closed OUTSIDE the segments' large contexts (an `omega` there case-splits every disjunction in
scope: EvRsh 515 s → seconds) -/
theorem bud_pre {rk b1 c rk' : Nat} (h1 : rk ≤ b1) (h2 : c + rk' ≤ rk) : c ≤ b1 := by omega
theorem bud_step {rk b1 c rk' b2 : Nat} (h1 : rk ≤ b1) (h2 : c + rk' ≤ rk) (h3 : b1 - c ≤ b2) : rk' ≤ b2 := by omega

theorem stkNat_a : segAddr Extracted.program StackNat.fn = 1784176 := by decide

theorem rnd_ge (n : Nat) : n ≤ StackNat.rnd n := by unfold StackNat.rnd; omega

theorem nlen_bd' {M : Memory} {p l n : Nat} (hN : NatNorm M p l) (hv : natVal M p l < 2 ^ (64 * n)) : l ≤ n := by
  rw [← SubMod2N.norm_nlen M p l hN]
  exact Exp.nlen_le_iff.2 (by simp only [Exp.B]; rw [← Nat.pow_mul]; exact hv)

/-- the join point `nat1R` (return of `m1 = stk.nat(n/64 + 1)`): scratch `m1 = (p, a1, a1)` -/
structure J1 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1
    (stLen s.mem st + StackNat.rnd (a1 (nE s mp ml))) rk
  pc : S.pc = BitVec.ofNat 64 nat1R
  r0 : S.regs 0 = BitVec.ofNat 64 p
  r1 : S.regs 1 = BitVec.ofNat 64 (a1 (nE s mp ml))
  r2 : S.regs 2 = BitVec.ofNat 64 (a1 (nE s mp ml))
  s224 : S.mem.readLE (sp + 224) 8 = a2 ml (nE s mp ml)
  d1 : DL R L s.mem st S.mem L1 p (a1 (nE s mp ml))

/-- the join point `lshR` (return of `m1 = m1.lsh(natOne, n)`): `m1 = (p1, l1, c1)` of value `2^n` -/
structure J2 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1
    (stLen s.mem st + StackNat.rnd (a1 (nE s mp ml))) rk
  pc : S.pc = BitVec.ofNat 64 lshR
  r0 : S.regs 0 = BitVec.ofNat 64 p1
  r1 : S.regs 1 = BitVec.ofNat 64 l1
  r2 : S.regs 2 = BitVec.ofNat 64 c1
  s224 : S.mem.readLE (sp + 224) 8 = a2 ml (nE s mp ml)
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1

/-- the level after `m1` and `m2 = stk.nat(ml - n/64)` -/
@[reducible] def ℓ2 (s : State) (st mp ml : Nat) : Nat :=
  stLen s.mem st + StackNat.rnd (a1 (nE s mp ml)) + StackNat.rnd (a2 ml (nE s mp ml))

/-- the join point `nat2R` (return of `m2 = stk.nat(ml - n/64)`): `m1` in the slots `288/208/216`, scratch
`m2 = (q, a2, a2)` apart from `m1` -/
structure J3 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ2 s st mp ml) rk
  pc : S.pc = BitVec.ofNat 64 nat2R
  r0 : S.regs 0 = BitVec.ofNat 64 q
  r1 : S.regs 1 = BitVec.ofNat 64 (a2 ml (nE s mp ml))
  r2 : S.regs 2 = BitVec.ofNat 64 (a2 ml (nE s mp ml))
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  d2 : DL R L s.mem st S.mem L1 q (a2 ml (nE s mp ml))
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)

/-- the join point `rshR` (return of `m2 = m2.rsh(m, n)`): `m1` in the slots, `m2 = (q, l2, a2)` of value
`M / 2^n` in its own (scratch) array -/
structure J4 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ2 s st mp ml) rk
  pc : S.pc = BitVec.ofNat 64 rshR
  r0 : S.regs 0 = BitVec.ofNat 64 q
  r1 : S.regs 1 = BitVec.ofNat 64 l2
  r2 : S.regs 2 = BitVec.ofNat 64 (a2 ml (nE s mp ml))
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)

/-- the level after `z1 = stk.nat(2 max(len m1, len m2))` -/
@[reducible] def ℓ3 (s : State) (st mp ml l1 l2 : Nat) : Nat := ℓ2 s st mp ml + StackNat.rnd (2 * max l1 l2)

/-- the join point `nat3R` (return of `z1 = stk.nat(2·max(len m1, len m2))`): `m1`, `m2` in their slots, slot 224
= `2·max`, scratch `z1 = (r, 2·max, 2·max)` apart from both -/
structure J5 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 r : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ3 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 nat3R
  r0 : S.regs 0 = BitVec.ofNat 64 r
  r1 : S.regs 1 = BitVec.ofNat 64 (2 * max l1 l2)
  r2 : S.regs 2 = BitVec.ofNat 64 (2 * max l1 l2)
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s224 : S.mem.readLE (sp + 224) 8 = 2 * max l1 l2
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  d3 : DL R L s.mem st S.mem L1 r (2 * max l1 l2)
  ap1 : Apart r (8 * (2 * max l1 l2)) p1 (8 * c1)
  ap2 : Apart r (8 * (2 * max l1 l2)) q (8 * a2 ml (nE s mp ml))

end FvModexp.Arm64.ExpEven
