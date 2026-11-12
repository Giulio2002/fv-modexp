import FvModexp.Proofs.Arm64.Exp.EvLN

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
    (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88) :
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
    (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88) :
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
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 88 ≤ a ∧ a + k ≤ sp + 448) → S'.mem.readLE a k = S.mem.readLE a k)
    (hsp8 : 8 ≤ sp) (hb : rk' ≤ b2) : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S' L2 b2 ℓ rk' :=
  ⟨esp.trans h.esp, e28.trans h.e28, e29.trans h.e29, e18.trans h.e18, hw,
    h.esl.keep (fun a k ha => hk a k (by simp only [SlotR] at ha; omega)) hsp8, hb⟩

/-- a range apart from `[b, b + k)` is outside it -/
theorem out1_of_apart {a n b k : Nat} (h : Apart b k a n) : Outside a n [(b, b + k)] := by
  unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the stack header is outside a callee window at `SP = sp` -/
theorem EPre.st_cw {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 88) : Outside st 24 [(sp - stk, sp - 8), (sp + 8, sp + above)] := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  simp only [outside_cons, outside_nil, and_true]; omega

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

end FvModexp.Arm64.ExpEven
