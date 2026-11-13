import FvModexp.Proofs.Arm64.Exp.EvJ13

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join `mul2R` (after `u = z1.mul(stk, z2, m2)`) (agent infra)

`J14` (`mul2R`, `X0..X2` = `u = (pu, lu, cu)`, value `(t mod 2^n) · m2`): only `z` (slots `272/168/176`) is still
needed; `u` located (`z3`'s array or fresh), `EL`, apart from `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the value of `u = (t mod 2^n) · m2` -/
@[reducible] def vU (s : State) (xp xl yp yl mp ml : Nat) : Nat :=
  vT s xp xl yp yl mp ml % 2 ^ nE s mp ml * (natVal s.mem mp ml / 2 ^ nE s mp ml)

/-- the join point `mul2R` (return of `z1.mul(stk, z2, m2)`): `X0..X2` = `u` -/
structure J14 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 lw pZ cZ pu lu cu : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 mul2R
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 pu
  r1 : S.regs 1 = BitVec.ofNat 64 lu
  r2 : S.regs 2 = BitVec.ofNat 64 cu
  s272 : S.mem.readLE (sp + 272) 8 = pZ
  s168 : S.mem.readLE (sp + 168) 8 = lw
  s176 : S.mem.readLE (sp + 176) 8 = cZ
  zs : LZ R L st zp zc S.mem L1 pZ lw cZ (vZ2 s xp xl yp yl mp ml)
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  u : LN R L s.mem st S.mem L1 pu lu cu (vU s xp xl yp yl mp ml)
  pu64 : pu < 2 ^ 64
  ue : EL R L pu cu
  uz : 0 < cu → 0 < cZ → Apart pu (8 * cu) pZ (8 * cZ)

end FvModexp.Arm64.ExpEven
