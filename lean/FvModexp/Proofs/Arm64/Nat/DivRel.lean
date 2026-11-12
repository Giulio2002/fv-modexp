import FvModexp.Proofs.Arm64.Nat.DivDefs

/-!
# `nat.div` (arm64): the segment-boundary relations (shared by the path modules)

`SP = s.sp` (entry), `SP' = SP - 240`. `AtW`: after `divW` returned (`fn + 0x6c`); `AtC`: after `nat.cmp` returned
(`fn + 0x140`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatDiv

/-- `divW`'s return site -/
abbrev retW : Nat := 0x1b926c
/-- `nat.cmp`'s return site -/
abbrev retC : Nat := 0x1b9340
/-- `divLarge`'s return site -/
abbrev retL : Nat := 0x1b94d4
/-- `nat.cmp`'s entry -/
abbrev cmpE : Nat := 1782608

/-- the frame ranges written before the first call: saved `X29`/`X30`, locals, spills -/
@[reducible] def proW (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 248, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 112)]

/-- the facts after `divW` returned (`len v = 1`): `q = (q, ql, qc)` with `U / V`, `X3 = U % V` -/
structure AtW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc z2 z2c u ul v vl : Nat) (s : State)
    (q ql qc : Nat) (L' : List (Nat × Nat)) (b' : Nat) (T : State) : Prop where
  pc : T.pc = BitVec.ofNat 64 retW
  sp : T.sp = s.sp - 240#64
  r28 : T.regs 28 = s.regs 28
  r29 : T.regs 29 = s.sp - 248#64
  r18 : T.regs 18 = s.regs 18
  r0 : T.regs 0 = BitVec.ofNat 64 q
  r1 : T.regs 1 = BitVec.ofNat 64 ql
  r2 : T.regs 2 = BitVec.ofNat 64 qc
  r3 : (T.regs 3).toNat = natVal s.mem u ul % natVal s.mem v vl
  hq : ExpHyp.NatOF R L L' T.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl)
  ext : LiveExt R L L'
  bud : b - makeCost ul ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' T.mem)
  mf : MemFrame s.mem T.mem (R.rt ++ winA s 41504 112 ++ ar zp zc)
  lf : LiveFrame s.mem T.mem L (ar zp zc)
  reg : T.mem.regions = s.mem.regions
  lr : T.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : T.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  s5 : T.mem.readLE (s.sp.toNat + 40) 8 = z2
  s7 : T.mem.readLE (s.sp.toNat + 56) 8 = z2c

/-- the facts after `nat.cmp` returned (`len v ≥ 2`): only the window written, `X0` = the comparison -/
structure AtC (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s S : State) : Prop where
  pc : S.pc = BitVec.ofNat 64 retC
  sp : S.sp = s.sp - 240#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 248#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = CmpSum.cmpRes ul vl (s.mem.readLE u (8 * ul)) (s.mem.readLE v (8 * vl))
  mf : MemFrame s.mem S.mem (winA s 41504 112)
  reg : S.mem.regions = s.mem.regions
  lr : S.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : S.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  s1 : S.mem.readLE (s.sp.toNat + 8) 8 = zp
  s2 : S.mem.readLE (s.sp.toNat + 16) 8 = zl
  s3 : S.mem.readLE (s.sp.toNat + 24) 8 = zc
  s4 : S.mem.readLE (s.sp.toNat + 32) 8 = st
  s5 : S.mem.readLE (s.sp.toNat + 40) 8 = z2
  s6 : S.mem.readLE (s.sp.toNat + 48) 8 = z2l
  s7 : S.mem.readLE (s.sp.toNat + 56) 8 = z2c
  s8 : S.mem.readLE (s.sp.toNat + 64) 8 = u
  s9 : S.mem.readLE (s.sp.toNat + 72) 8 = ul
  s10 : S.mem.readLE (s.sp.toNat + 80) 8 = uc
  s11 : S.mem.readLE (s.sp.toNat + 88) 8 = v
  s12 : S.mem.readLE (s.sp.toNat + 96) 8 = vl
  s13 : S.mem.readLE (s.sp.toNat + 104) 8 = vc

end FvModexp.Arm64.NatDiv
