import FvModexp.Proofs.Amd64.Exp.EvJ10
import FvModexp.Proofs.Amd64.Exp.ModInvDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the join `miR` (after `m2inv := m1.modularInverseModPowerOfTwo(stk, m2, n)`) (asm s62;
twin of infra's arm64 `EvJ11`)

* `MiEns impl R kc sqrC mulC`: infra's planned amd64 `ModInv.ens` conclusion (NOTES-conventions "[infra s55]"): the
  Q-form `ModInv.PreQ` / `ModInv.PostQ` (Amd64/Exp/ModInvDefs.lean) for every reserve level `H` and budget `B`, on
  `LibW.names` (it leaves out `expNNEven`). It stays a PREMISE of the Even chain.
* `J11` (`miR`, `RAX/RBX/RCX` = `m2inv = (p4, l4, c4)`, value `ModInv.val (M / 2^n) n`): `m2`, `z2`, `z`, `z3` kept
  (`z3` now also in the slots `0x100/0x90/0x98`); `m1`'s array is consumed; `m2inv` located and apart from the others.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `ModInv.ens`'s conclusion (every instance; amd64 Q form) -/
def MiEns (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) :
    Prop :=
  ∀ (H B : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat),
    Ensures ((Extracted.program.onlySegments LibW.names).link impl) (segAddr Extracted.program ModInv.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (ModInv.PreQ R kc H sqrC mulC B L zp zl zc st xp xl xc n) (ModInv.PostQ R kc H sqrC mulC B L zp zc st xp xl n)

/-- `nat.modularInverseModPowerOfTwo`'s entry -/
abbrev miE : Nat := 0x5ea8c0

theorem modInv_a : segAddr Extracted.program ModInv.fn = miE := by decide

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
structure J11 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 miR
  l1m : l1 ≤ ml
  r0 : S.regs 0 = BitVec.ofNat 64 p4
  r3 : S.regs 3 = BitVec.ofNat 64 l4
  r1 : S.regs 1 = BitVec.ofNat 64 c4
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  sf8 : S.mem.readLE (sp + 0xf8) 8 = pw
  s80 : S.mem.readLE (sp + 0x80) 8 = lw
  s88 : S.mem.readLE (sp + 0x88) 8 = cw
  s108 : S.mem.readLE (sp + 0x108) 8 = pZ
  sa0 : S.mem.readLE (sp + 0xa0) 8 = lw
  sa8 : S.mem.readLE (sp + 0xa8) 8 = cZ
  s100 : S.mem.readLE (sp + 0x100) 8 = p3
  s90 : S.mem.readLE (sp + 0x90) 8 = l3
  s98 : S.mem.readLE (sp + 0x98) 8 = c3
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


end FvModexp.Amd64.ExpEven
