import FvModexp.Proofs.Arm64.Exp.EvJ2

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join point after the second `nat.expNN` call (agent infra)

* `J8` (`exp2R`): `J7`'s locals (`m1`, `m2`, `z1` in their slots) and `z2 = x^y mod m2` in `X0..X2`, its array apart
  from `m1`, `m2` and `z1`'s array; an empty `z2` (possibly `nil`) is carried by its register value only.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the join point `exp2R` (return of `z2 = z2.expNN(stk, x, y, m2, false)`) -/
structure J8 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 exp2R
  r0 : S.regs 0 = BitVec.ofNat 64 pw
  r1 : S.regs 1 = BitVec.ofNat 64 lw
  r2 : S.regs 2 = BitVec.ofNat 64 cw
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s224 : S.mem.readLE (sp + 224) 8 = 2 * max l1 l2
  s264 : S.mem.readLE (sp + 264) 8 = pz
  s152 : S.mem.readLE (sp + 152) 8 = lz
  s160 : S.mem.readLE (sp + 160) 8 = cz
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  pz64 : pz < 2 ^ 64
  z1e : EL R L pz cz
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  z2 : LN R L s.mem st S.mem L1 pw lw cw
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pw64 : pw < 2 ^ 64
  z2e : EL R L pw cw
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)

end FvModexp.Arm64.ExpEven
