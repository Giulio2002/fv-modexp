import FvModexp.Proofs.Amd64.Exp.EvRel
import FvModexp.Proofs.Common.ExpPow2
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the join points `nat1R` … `nat3R` (asm s57; port of infra's arm64 `EvJ`)

`JX` = the facts common to every join point (`RSP = sp`, `R14 = g`, `fsBase`, `X15 = 0`, `DF = 0`, the context `WC`
at level `ℓ`, the slots `ESl`, the defer bit `[sp + 0x77] = 1`, the remaining budget `rk ≤ b1`). `Jk` = `JX` + the
live locals at the return of call `k` (pc, result registers, local slots; slot map: `EvDefs`). Every callee runs at
`RSP = sp - 8` with `above ≤ 0x7f` (so `[sp + 0x77, sp + 0x1b8)` survives: `JX.call`).
`LN.rd` / `DL.wr`: a local as a callee's input (`RdIn`) / destination (`WrOut`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `n = tz(m)` -/
@[reducible] def nE (s : State) (mp ml : Nat) : Nat := Exp.tz (natVal s.mem mp ml)

/-- the facts common to every join point -/
structure JX (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 ℓ rk : Nat) : Prop where
  esp : S.regs 4 = BitVec.ofNat 64 sp
  e14 : S.regs 14 = BitVec.ofNat 64 g
  efs : S.fsBase.toNat = fs
  ex15 : S.xmm 15 = 0
  edf : S.df = false
  wc : WC R L K g sp st zp zc s.mem S.mem L1 b1 ℓ
  esl : ESl S.mem sp st bp r zp zc xp xl xc yp yl yc mp ml mc (stLen s.mem st) (nE s mp ml)
  dfb : S.mem.readLE (sp + 0x77) 1 = 1
  bud : rk ≤ b1

theorem tz_lt {X ml : Nat} (h0 : 0 < X) (h : X < 2 ^ (64 * ml)) : Exp.tz X < 64 * ml := by
  have hs := (Exp.tz_spec h0).1
  have hq : 0 < X / 2 ^ Exp.tz X := by
    rcases Nat.eq_zero_or_pos (X / 2 ^ Exp.tz X) with e | e
    · rw [e, Nat.mul_zero] at hs; omega
    · exact e
  have : 2 ^ Exp.tz X ≤ X := by
    calc 2 ^ Exp.tz X ≤ 2 ^ Exp.tz X * (X / 2 ^ Exp.tz X) := Nat.le_mul_of_pos_right _ hq
      _ = X := hs.symm
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt this h)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a live local (`0 < c`) as a callee input at `RSP = sp - 8` -/
theorem LN.rd (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {p l c v : Nat} (h : LN R L s.mem st M L1 p l c v) (hc : 0 < c) {S : State}
    (hsp : (S.regs 4).toNat = sp - 8) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x7f) :
    EvenHyp.RdIn R L1 S stk above p l := by
  have hk := hP.kf
  obtain ⟨⟨c40, hlv, hlo⟩, hlc, -, -⟩ := h
  obtain ⟨-, a2, a3, a4⟩ := hlv hc
  obtain ⟨w1, -⟩ := Loc.ap hP (hlo hc).1
  unfold Apart at w1
  subst hm
  refine ⟨by omega, Janus.Arm64.Memory.accessible_weaken _
    (Janus.Arm64.Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega)), by omega, a2.sub (by omega) (by omega), ?_⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- a destination as a callee's output array at `RSP = sp - 8` -/
theorem DL.wr (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {p c : Nat} (h : DL R L s.mem st M L1 p c) {S : State} (hsp : (S.regs 4).toNat = sp - 8)
    (h14 : (S.regs 14).toNat = g) (hfs : S.fsBase.toNat = fs) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 0x7f) :
    EvenHyp.WrOut R L1 S stk above p c := by
  have hk := hP.kf
  obtain ⟨c40, hlv, hlo⟩ := h
  subst hm
  refine ⟨c40, hlv, fun hc => ?_⟩
  obtain ⟨w1, -, w3, w4, -⟩ := Loc.ap hP (hlo hc).1
  unfold Apart at w1
  refine ⟨?_, by rw [h14]; exact w3, by rw [hfs]; exact w4⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- the stack header is outside a callee window at `RSP = sp - 8` -/
theorem EPre.st_cw (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 0x7f) : Outside st 24 [(sp - 8 - stk, sp - 8 + above)] := by
  have hk := hP.kf
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  simp only [outside_cons, outside_nil, and_true]; omega

/-- `n = tz M ∈ [1, 64 ml)` for an even positive `M` -/
theorem nE_bd (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) : 0 < nE s mp ml ∧ nE s mp ml < 64 * ml := by
  have hlt : natVal s.mem mp ml < 2 ^ (64 * ml) := by
    have := Janus.Arm64.Memory.readLE_lt s.mem mp (8 * ml)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * ml) = 64 * ml by omega] at this
    exact this
  refine ⟨?_, tz_lt hM hlt⟩
  show 0 < Exp.tz (natVal s.mem mp ml)
  rw [Exp.tz_even (by omega) hev]; omega

end

/-- a located array (`0 < k`) is apart from a range held at the entry and apart from the entry free part -/
theorem Loc.apart {R : RtInv} {L : List (Nat × Nat)} {m0 : Memory} {st t k a n : Nat} (h : Loc R L m0 st t k)
    (hk : 0 < k) (hh : Held R L a n)
    (hf : stLen m0 st < stCap m0 st → Apart a n (stW m0 st + 8 * stLen m0 st) (8 * (stCap m0 st - stLen m0 st))) :
    Apart t (8 * k) a n := by
  rcases h with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · have := hf (by omega); unfold Apart at this ⊢; omega
  · exact hfresh hh hap hin

/-- `JX` through a callee step (registers kept, the new context, the window above `sp + 0x77` kept) -/
theorem JX.call {R : RtInv} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s S : State} {L1 : List (Nat × Nat)} {b1 ℓ rk : Nat}
    (h : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 ℓ rk) {S' : State}
    {L2 : List (Nat × Nat)} {b2 rk' : Nat}
    (esp : S'.regs 4 = S.regs 4) (e14 : S'.regs 14 = S.regs 14) (efs : S'.fsBase = S.fsBase)
    (ex15 : S'.xmm 15 = S.xmm 15) (edf : S'.df = S.df)
    (hw : WC R L K g sp st zp zc s.mem S'.mem L2 b2 ℓ)
    (hk : ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → S'.mem.readLE a k = S.mem.readLE a k)
    (hb : rk' ≤ b2) : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 ℓ rk' :=
  ⟨esp.trans h.esp, e14.trans h.e14, by rw [efs]; exact h.efs, ex15.trans h.ex15, edf.trans h.edf, hw,
    h.esl.keep (fun a k ha => hk a k (by simp only [SlotR] at ha; omega) (by simp only [SlotR] at ha; omega)),
    by rw [hk _ _ (Nat.le_refl _) (by omega)]; exact h.dfb, hb⟩

/-- a range apart from `[b, b + k)` is outside it -/
theorem out1_of_apart {a n b k : Nat} (h : Apart b k a n) : Outside a n [(b, b + k)] := by
  unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- a store range of the function's own frame -/
@[reducible] def OwnR (sp K : Nat) (r : Nat × Nat) : Prop :=
  r.1 ≤ r.2 ∧ (sp - 8 - K ≤ r.1 ∧ r.2 ≤ sp + 0x148 ∨ sp + 0x180 ≤ r.1 ∧ r.2 ≤ sp + 0x1b8)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `WC` and every live local through the function's own stores -/
theorem WC.own (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory}
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions) (hws : ∀ r ∈ ws, OwnR sp K r) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ ∧
      ∀ q l c v, LN R L s.mem st M L1 q l c v → LN R L s.mem st M' L1 q l c v := by
  have hk := hP.kf
  have hLs : LiveSep L [(sp - 8 - K, sp - 8 + 0x1c0)] := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  have hwin : ∀ a k, (a + k ≤ sp - 8 - K ∨ sp + 0x1b8 ≤ a) → Outside a k ws := by
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

/-- budget steps, closed OUTSIDE the segments' large contexts -/
theorem bud_pre {rk b1 c rk' : Nat} (h1 : rk ≤ b1) (h2 : c + rk' ≤ rk) : c ≤ b1 := by omega
theorem bud_step {rk b1 c rk' b2 : Nat} (h1 : rk ≤ b1) (h2 : c + rk' ≤ rk) (h3 : b1 - c ≤ b2) : rk' ≤ b2 := by omega

theorem stkNat_a : segAddr Extracted.program StackNat.fn = 0x5e6480 := by decide

theorem rnd_ge (n : Nat) : n ≤ StackNat.rnd n := by unfold StackNat.rnd; omega

theorem nlen_bd' {M : Memory} {p l n : Nat} (hN : NatNorm M p l) (hv : natVal M p l < 2 ^ (64 * n)) : l ≤ n := by
  rw [← SubMod2N.norm_nlen M p l hN]
  exact Exp.nlen_le_iff.2 (by simp only [Exp.B]; rw [← Nat.pow_mul]; exact hv)

/-- the join point `nat1R` (return of `m1 = stk.nat(n/64 + 1)`): scratch `m1 = (p, a1, a1)`; slot `0xd8 = a2` -/
structure J1 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
    (stLen s.mem st + StackNat.rnd (a1 (nE s mp ml))) rk
  pc : S.rip = BitVec.ofNat 64 nat1R
  r0 : S.regs 0 = BitVec.ofNat 64 p
  r3 : S.regs 3 = BitVec.ofNat 64 (a1 (nE s mp ml))
  r1 : S.regs 1 = BitVec.ofNat 64 (a1 (nE s mp ml))
  sd8 : S.mem.readLE (sp + 0xd8) 8 = a2 ml (nE s mp ml)
  d1 : DL R L s.mem st S.mem L1 p (a1 (nE s mp ml))

/-- the join point `lshR` (return of `m1 = m1.lsh(natOne, n)`): `m1 = (p1, l1, c1)` of value `2^n` -/
structure J2 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
    (stLen s.mem st + StackNat.rnd (a1 (nE s mp ml))) rk
  pc : S.rip = BitVec.ofNat 64 lshR
  r0 : S.regs 0 = BitVec.ofNat 64 p1
  r3 : S.regs 3 = BitVec.ofNat 64 l1
  r1 : S.regs 1 = BitVec.ofNat 64 c1
  sd8 : S.mem.readLE (sp + 0xd8) 8 = a2 ml (nE s mp ml)
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1

/-- the level after `m1` and `m2 = stk.nat(ml - n/64)` -/
@[reducible] def lvl2 (s : State) (st mp ml : Nat) : Nat :=
  stLen s.mem st + StackNat.rnd (a1 (nE s mp ml)) + StackNat.rnd (a2 ml (nE s mp ml))

/-- the join point `nat2R` (return of `m2 = stk.nat(ml - n/64)`): `m1` in the slots `0x118/0xc8/0xd0`, scratch
`m2 = (q, a2, a2)` apart from `m1` -/
structure J3 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl2 s st mp ml) rk
  pc : S.rip = BitVec.ofNat 64 nat2R
  r0 : S.regs 0 = BitVec.ofNat 64 q
  r3 : S.regs 3 = BitVec.ofNat 64 (a2 ml (nE s mp ml))
  r1 : S.regs 1 = BitVec.ofNat 64 (a2 ml (nE s mp ml))
  s118 : S.mem.readLE (sp + 0x118) 8 = p1
  sc8 : S.mem.readLE (sp + 0xc8) 8 = l1
  sd0 : S.mem.readLE (sp + 0xd0) 8 = c1
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  d2 : DL R L s.mem st S.mem L1 q (a2 ml (nE s mp ml))
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)

/-- the join point `rshR` (return of `m2 = m2.rsh(m, n)`): `m1` in the slots, `m2 = (q, l2, a2)` of value
`M / 2^n` in its own (scratch) array -/
structure J4 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl2 s st mp ml) rk
  pc : S.rip = BitVec.ofNat 64 rshR
  r0 : S.regs 0 = BitVec.ofNat 64 q
  r3 : S.regs 3 = BitVec.ofNat 64 l2
  r1 : S.regs 1 = BitVec.ofNat 64 (a2 ml (nE s mp ml))
  s118 : S.mem.readLE (sp + 0x118) 8 = p1
  sc8 : S.mem.readLE (sp + 0xc8) 8 = l1
  sd0 : S.mem.readLE (sp + 0xd0) 8 = c1
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)

/-- the level after `z1 = stk.nat(2 max(len m1, len m2))` -/
@[reducible] def lvl3 (s : State) (st mp ml l1 l2 : Nat) : Nat := lvl2 s st mp ml + StackNat.rnd (2 * max l1 l2)

/-- the join point `nat3R` (return of `z1 = stk.nat(2·max(len m1, len m2))`): `m1`, `m2` in their slots, slot
`0xd8 = 2·max`, scratch `z1 = (t, 2·max, 2·max)` apart from both -/
structure J5 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 t : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl3 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 nat3R
  r0 : S.regs 0 = BitVec.ofNat 64 t
  r3 : S.regs 3 = BitVec.ofNat 64 (2 * max l1 l2)
  r1 : S.regs 1 = BitVec.ofNat 64 (2 * max l1 l2)
  s118 : S.mem.readLE (sp + 0x118) 8 = p1
  sc8 : S.mem.readLE (sp + 0xc8) 8 = l1
  sd0 : S.mem.readLE (sp + 0xd0) 8 = c1
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  sd8 : S.mem.readLE (sp + 0xd8) 8 = 2 * max l1 l2
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  d3 : DL R L s.mem st S.mem L1 t (2 * max l1 l2)
  ap1 : Apart t (8 * (2 * max l1 l2)) p1 (8 * c1)
  ap2 : Apart t (8 * (2 * max l1 l2)) q (8 * a2 ml (nE s mp ml))

end FvModexp.Amd64.ExpEven
