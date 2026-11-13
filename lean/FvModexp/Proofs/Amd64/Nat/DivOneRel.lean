import FvModexp.Proofs.Amd64.Nat.DivCmp

set_option autoImplicit false

/-!
# `nat.div` (amd64), `len v = 1`: the segment-boundary relations of the `divW` path (natdiv.go:523-529)

`AtV`: at `nat.divW`'s entry (`fn + 0xb1` called it; return address `retW = fn + 0xb6` at `SP - 240`); `AtW`: after
`divW` returned (`RSP = SP' = SP - 232`), `q` in `RAX, RBX, RCX`, `r2` in `RDI`. Spills used afterwards: `z2` at
`SP + 88`, `cap z2` at `SP + 104` (`MOVQ R9, 0x150(SP')`). Port of `Arm64/Nat/DivRel.lean`'s `AtW`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatDiv

/-- `nat.divW`'s return site (`fn + 0xb6`) -/
abbrev retW : Nat := 0x5edfd6
/-- `nat.divW`'s entry -/
abbrev divWE : Nat := 6218944

theorem divWE_eq : segAddr Extracted.program DivW.fn = divWE := by decide

/-- the state at `nat.divW`'s entry (`len v = 1`) -/
structure AtV (zp zl zc z2 z2c u ul uc v : Nat) (s X : State) : Prop where
  pc : X.rip = BitVec.ofNat 64 divWE
  sp : X.regs 4 = s.regs 4 - 240#64
  r5 : X.regs 5 = s.regs 4 - 8#64
  r14 : X.regs 14 = s.regs 14
  fs : X.fsBase = s.fsBase
  x15 : X.xmm 15 = 0#128
  df : X.df = false
  a0 : X.regs 0 = BitVec.ofNat 64 zp
  a3 : X.regs 3 = BitVec.ofNat 64 zl
  a1 : X.regs 1 = BitVec.ofNat 64 zc
  a7 : X.regs 7 = BitVec.ofNat 64 u
  a6 : X.regs 6 = BitVec.ofNat 64 ul
  a8 : X.regs 8 = BitVec.ofNat 64 uc
  a9 : X.regs 9 = BitVec.ofNat 64 (s.mem.readLE v 8)
  rc : X.mem.readLE ((s.regs 4).toNat - 240) 8 = retW
  mf : MemFrame s.mem X.mem (proW s)
  reg : X.mem.regions = s.mem.regions
  bp : X.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  s5 : X.mem.readLE ((s.regs 4).toNat + 88) 8 = z2
  s7 : X.mem.readLE ((s.regs 4).toNat + 104) 8 = z2c

/-- after `nat.divW` returned: `q` (`RAX, RBX, RCX`) = `U / V` in `z`'s array or a fresh one, `RDI = U % V` -/
structure AtW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc z2 z2c u ul v vl : Nat) (s : State)
    (q ql qc : Nat) (L' : List (Nat × Nat)) (b' : Nat) (T : State) : Prop where
  pc : T.rip = BitVec.ofNat 64 retW
  sp : T.regs 4 = s.regs 4 - 232#64
  r5 : T.regs 5 = s.regs 4 - 8#64
  r14 : T.regs 14 = s.regs 14
  fs : T.fsBase = s.fsBase
  x15 : T.xmm 15 = 0#128
  df : T.df = false
  r0 : T.regs 0 = BitVec.ofNat 64 q
  r3 : T.regs 3 = BitVec.ofNat 64 ql
  r1 : T.regs 1 = BitVec.ofNat 64 qc
  r7 : (T.regs 7).toNat = natVal s.mem u ul % natVal s.mem v vl
  hq : ExpHyp.NatOF R L L' T.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl)
  ext : LiveExt R L L'
  bud : b - makeCost ul ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' T.mem)
  mf : MemFrame s.mem T.mem (R.rt ++ win s 41512 112 ++ ar zp zc)
  lf : LiveFrame s.mem T.mem L (ar zp zc)
  reg : T.mem.regions = s.mem.regions
  ra : T.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : T.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  s5 : T.mem.readLE ((s.regs 4).toNat + 88) 8 = z2
  s7 : T.mem.readLE ((s.regs 4).toNat + 104) 8 = z2c

end FvModexp.Amd64.NatDiv
