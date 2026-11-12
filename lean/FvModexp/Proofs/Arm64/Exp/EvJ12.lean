import FvModexp.Proofs.Arm64.Exp.EvJ11

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join `mul1R` (after `z2 = z2.mul(stk, z1, m2inv)`) (agent infra)

`J12` (`mul1R`, `X0..X2` = the product `t = (pt, lt, ct)`, value `vZ3 · vMi`): `m2`, `z`, `z3` kept (slots
`280/192/200`, `272/168/176`, `264/152/160`); `t` located (`z2`'s array or fresh), `EL`, apart from `m2`, `z`, `z3`.
`mi_lt`: `m2inv < 2^n`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem mi_lt (X n : Nat) : ModInv.val X n < 2 ^ n := by
  simp only [ModInv.val, Exp.modularInverseModPowerOfTwo]
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos n)
  · exact (Exp.subMod2N_spec _ _ _).1

theorem mi_pos {X n : Nat} (hX : X % 2 = 1) (hn : 0 < n) : 0 < ModInv.val X n := by
  have h := Exp.modularInverseModPowerOfTwo_spec X n hX hn
  rcases Nat.eq_zero_or_pos (ModInv.val X n) with e | e
  · simp only [ModInv.val] at e
    rw [e, Nat.mul_zero, Nat.zero_mod, Nat.one_mod_eq_one.mpr (by have := Nat.one_lt_two_pow (n := n) (by omega); omega)] at h
    exact absurd h (by decide)
  · exact e

/-- a result `(p', c')` of `NatOF` form below `2^64` (the destination's pointer is, and a fresh result is non-empty) -/
theorem natOF_p64 {M : Memory} {R : RtInv} {L L' : List (Nat × Nat)} {zp zc need p' c' : Nat}
    (hor : (p' = zp ∧ c' = zc) ∨ (need ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hlv : NatLive M R L' p' c') (hzp : zp < 2 ^ 64) (hneed : 0 < need) : p' < 2 ^ 64 := by
  rcases hor with ⟨rfl, -⟩ | ⟨hn, -⟩
  · exact hzp
  · have := (hlv (by omega)).2.2.2; omega

/-- the value of `t = z3 · m2inv` -/
@[reducible] def vT (s : State) (xp xl yp yl mp ml : Nat) : Nat := vZ3 s xp xl yp yl mp ml * vMi s mp ml

/-- the join point `mul1R` (return of `z2.mul(stk, z1, m2inv)`): `X0..X2` = `t` -/
structure J12 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 mul1R
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 pt
  r1 : S.regs 1 = BitVec.ofNat 64 lt
  r2 : S.regs 2 = BitVec.ofNat 64 ct
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s272 : S.mem.readLE (sp + 272) 8 = pZ
  s168 : S.mem.readLE (sp + 168) 8 = lw
  s176 : S.mem.readLE (sp + 176) 8 = cZ
  s264 : S.mem.readLE (sp + 264) 8 = p3
  s152 : S.mem.readLE (sp + 152) 8 = l3
  s160 : S.mem.readLE (sp + 160) 8 = c3
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  zs : LZ R L st zp zc S.mem L1 pZ lw cZ (vZ2 s xp xl yp yl mp ml)
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  z3 : LN R L s.mem st S.mem L1 p3 l3 c3 (vZ3 s xp xl yp yl mp ml)
  p364 : p3 < 2 ^ 64
  z3e : EL R L p3 c3
  ta2 : 0 < c3 → Apart p3 (8 * c3) q (8 * a2 ml (nE s mp ml))
  tZ : 0 < c3 → 0 < cZ → Apart p3 (8 * c3) pZ (8 * cZ)
  t : LN R L s.mem st S.mem L1 pt lt ct (vT s xp xl yp yl mp ml)
  pt64 : pt < 2 ^ 64
  te : EL R L pt ct
  tq : 0 < ct → Apart pt (8 * ct) q (8 * a2 ml (nE s mp ml))
  tz : 0 < ct → 0 < cZ → Apart pt (8 * ct) pZ (8 * cZ)
  t3 : 0 < ct → 0 < c3 → Apart pt (8 * ct) p3 (8 * c3)

end FvModexp.Arm64.ExpEven
