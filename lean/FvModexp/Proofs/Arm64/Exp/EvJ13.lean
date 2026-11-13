import FvModexp.Proofs.Arm64.Exp.EvJ12

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join `trR` (after `z2 = z2.trunc(z2, n)`) (agent infra)

`J13` = `J12` with the product truncated in place (`trunc` reuses `t`'s array: `need ≤ len t ≤ cap t`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the join point `trR` (return of `z2.trunc(z2, n)`): `X0..X2` = `t mod 2^n` in `t`'s array -/
structure J13 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lu ct : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 trR
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 pt
  r1 : S.regs 1 = BitVec.ofNat 64 lu
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
  t : LN R L s.mem st S.mem L1 pt lu ct (vT s xp xl yp yl mp ml % 2 ^ nE s mp ml)
  pt64 : pt < 2 ^ 64
  te : EL R L pt ct
  tq : 0 < ct → Apart pt (8 * ct) q (8 * a2 ml (nE s mp ml))
  tz : 0 < ct → 0 < cZ → Apart pt (8 * ct) pZ (8 * cZ)
  t3 : 0 < ct → 0 < c3 → Apart pt (8 * ct) p3 (8 * c3)

end FvModexp.Arm64.ExpEven
