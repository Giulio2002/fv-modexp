import FvModexp.Proofs.Amd64.Exp.EvJ11

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the joins `mul1R`, `trR`, `mul2R` (asm s63; twins of infra's arm64 `EvJ12`/`EvJ13`/`EvJ14`)

* `J12` (`mul1R`, `RAX/RBX/RCX` = the product `t = z3 · m2inv`): `m2`, `z`, `z3` kept (slots `0x110/0xb8/0xc0`,
  `0x108/0xa0/0xa8`, `0x100/0x90/0x98`); `t` located (`z2`'s array or fresh), `EL`, apart from `m2`, `z`, `z3`.
* `J13` (`trR`): `J12` with `t` truncated in place (`t mod 2^n`).
* `J14` (`mul2R`, `u = (t mod 2^n) · m2`): `z` kept; `u` located, apart from `z`.
Shared definitions module of the J11 → J15 segments (ROW-TIME LESSON).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

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

/-- the value of `t = z3 · m2inv` -/
@[reducible] def vT (s : State) (xp xl yp yl mp ml : Nat) : Nat := vZ3 s xp xl yp yl mp ml * vMi s mp ml

/-- the value of `u = (t mod 2^n) · m2` -/
@[reducible] def vU (s : State) (xp xl yp yl mp ml : Nat) : Nat :=
  vT s xp xl yp yl mp ml % 2 ^ nE s mp ml * (natVal s.mem mp ml / 2 ^ nE s mp ml)

/-- the join point `mul1R` (return of `z2.mul(stk, z3, m2inv)`): `RAX/RBX/RCX` = `t` -/
structure J12 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 mul1R
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 pt
  r3 : S.regs 3 = BitVec.ofNat 64 lt
  r1 : S.regs 1 = BitVec.ofNat 64 ct
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  s108 : S.mem.readLE (sp + 0x108) 8 = pZ
  sa0 : S.mem.readLE (sp + 0xa0) 8 = lw
  sa8 : S.mem.readLE (sp + 0xa8) 8 = cZ
  s100 : S.mem.readLE (sp + 0x100) 8 = p3
  s90 : S.mem.readLE (sp + 0x90) 8 = l3
  s98 : S.mem.readLE (sp + 0x98) 8 = c3
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

/-- the join point `trR` (return of `z2.trunc(z2, n)`): `RAX/RBX/RCX` = `t mod 2^n` in `t`'s array -/
structure J13 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lu ct : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 trR
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 pt
  r3 : S.regs 3 = BitVec.ofNat 64 lu
  r1 : S.regs 1 = BitVec.ofNat 64 ct
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  s108 : S.mem.readLE (sp + 0x108) 8 = pZ
  sa0 : S.mem.readLE (sp + 0xa0) 8 = lw
  sa8 : S.mem.readLE (sp + 0xa8) 8 = cZ
  s100 : S.mem.readLE (sp + 0x100) 8 = p3
  s90 : S.mem.readLE (sp + 0x90) 8 = l3
  s98 : S.mem.readLE (sp + 0x98) 8 = c3
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
  t : LN R L s.mem st S.mem L1 pt lu ct (vT s xp xl yp yl mp ml % 2 ^ nE s mp ml)
  pt64 : pt < 2 ^ 64
  te : EL R L pt ct
  tq : 0 < ct → Apart pt (8 * ct) q (8 * a2 ml (nE s mp ml))
  tz : 0 < ct → 0 < cZ → Apart pt (8 * ct) pZ (8 * cZ)
  t3 : 0 < ct → 0 < c3 → Apart pt (8 * ct) p3 (8 * c3)

/-- the join point `mul2R` (return of `z3.mul(stk, t, m2)`): `RAX/RBX/RCX` = `u` -/
structure J14 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 lw pZ cZ pu lu cu : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 mul2R
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 pu
  r3 : S.regs 3 = BitVec.ofNat 64 lu
  r1 : S.regs 1 = BitVec.ofNat 64 cu
  s108 : S.mem.readLE (sp + 0x108) 8 = pZ
  sa0 : S.mem.readLE (sp + 0xa0) 8 = lw
  sa8 : S.mem.readLE (sp + 0xa8) 8 = cZ
  zs : LZ R L st zp zc S.mem L1 pZ lw cZ (vZ2 s xp xl yp yl mp ml)
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  u : LN R L s.mem st S.mem L1 pu lu cu (vU s xp xl yp yl mp ml)
  pu64 : pu < 2 ^ 64
  ue : EL R L pu cu
  uz : 0 < cu → 0 < cZ → Apart pu (8 * cu) pZ (8 * cZ)

end FvModexp.Amd64.ExpEven
