import FvModexp.Proofs.Arm64.Exp.EvJ10
import FvModexp.Proofs.Arm64.Exp.ModInvDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join `miR` (after `m2inv := m1.modularInverseModPowerOfTwo(stk, m2, n)`) (agent infra)

* `MiEns impl R kc sqC mlC`: infra's `ModInv.ens` conclusion (the callee summary family on `LibW.names` = `ModInv.names`).
* `J11` (`miR`, `X0..X2` = `m2inv = (p4, l4, c4)`, value `ModInv.val (M / 2^n) n`): `m2`, `z2`, `z`, `z3` kept (the
  `subMod2N` result `z3` now also in the slots `264/152/160`); `m1`'s array is consumed (`m2inv` may reuse it); `m2inv`
  located and apart from `m2`, `z2`, `z`, `z3`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- `ModInv.ens`'s conclusion (every instance) -/
def MiEns (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (ℓ b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program ModInv.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (ModInv.PreL R kc sqC mlC ℓ b L zp zl zc st xp xl xc n) (ModInv.Post R kc (sqC ℓ) (mlC ℓ) b L zp zc st xp xl n)

theorem modInv_a : segAddr Extracted.program ModInv.fn = 1797104 := by decide

/-- the value of `m2inv` -/
@[reducible] def vMi (s : State) (mp ml : Nat) : Nat :=
  ModInv.val (natVal s.mem mp ml / 2 ^ nE s mp ml) (nE s mp ml)

/-- the value of `z3 = (z1 - z2) mod 2^n` -/
@[reducible] def vZ3 (s : State) (xp xl yp yl mp ml : Nat) : Nat :=
  Exp.subMod2N (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml)) (nE s mp ml)

/-- the value of `z2 = x^y mod m2` -/
@[reducible] def vZ2 (s : State) (xp xl yp yl mp ml : Nat) : Nat :=
  natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml)

/-- the join point `miR` (return of `m1.modularInverseModPowerOfTwo(stk, m2, n)`): `X0..X2` = `m2inv` -/
structure J11 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 miR
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 p4
  r1 : S.regs 1 = BitVec.ofNat 64 l4
  r2 : S.regs 2 = BitVec.ofNat 64 c4
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s256 : S.mem.readLE (sp + 256) 8 = pw
  s136 : S.mem.readLE (sp + 136) 8 = lw
  s144 : S.mem.readLE (sp + 144) 8 = cw
  s272 : S.mem.readLE (sp + 272) 8 = pZ
  s168 : S.mem.readLE (sp + 168) 8 = lw
  s176 : S.mem.readLE (sp + 176) 8 = cZ
  s264 : S.mem.readLE (sp + 264) 8 = p3
  s152 : S.mem.readLE (sp + 152) 8 = l3
  s160 : S.mem.readLE (sp + 160) 8 = c3
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  z2 : LN R L s.mem st S.mem L1 pw lw cw (vZ2 s xp xl yp yl mp ml)
  pw64 : pw < 2 ^ 64
  z2e : EL R L pw cw
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  zs : LZ R L st zp zc S.mem L1 pZ lw cZ (vZ2 s xp xl yp yl mp ml)
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)
  z3 : LN R L s.mem st S.mem L1 p3 l3 c3 (vZ3 s xp xl yp yl mp ml)
  p364 : p3 < 2 ^ 64
  z3e : EL R L p3 c3
  ta2 : 0 < c3 → Apart p3 (8 * c3) q (8 * a2 ml (nE s mp ml))
  tw : 0 < c3 → 0 < cw → Apart p3 (8 * c3) pw (8 * cw)
  tZ : 0 < c3 → 0 < cZ → Apart p3 (8 * c3) pZ (8 * cZ)
  mi : LN R L s.mem st S.mem L1 p4 l4 c4 (vMi s mp ml)
  p464 : p4 < 2 ^ 64
  mie : EL R L p4 c4
  ia2 : 0 < c4 → Apart p4 (8 * c4) q (8 * a2 ml (nE s mp ml))
  iw : 0 < c4 → 0 < cw → Apart p4 (8 * c4) pw (8 * cw)
  iZ : 0 < c4 → 0 < cZ → Apart p4 (8 * c4) pZ (8 * cZ)
  it : 0 < c4 → 0 < c3 → Apart p4 (8 * c4) p3 (8 * c3)

end FvModexp.Arm64.ExpEven
