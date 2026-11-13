import FvModexp.Proofs.Amd64.Nat.DivRel

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u ≥ v` (`len v ≥ 2`): the state at `divLarge`'s entry (`AtL`)

From `AtC` (`cmp ≥ 0`, `JGE fn + 0x321`): `stk ≠ nil` → `AL = 0` (no deferred `putStack`), `MOVB AL, [SP' + 0x6e]`
(`RSP - 122`); the stack args `u`, `v` copied to `SP' + 0 … 0x28` (`RSP - 232 … - 184`); `z` = `RAX, RBX, RCX`,
`stk` = `RDI`, `z2` = `RSI, R8, R9`; `CALL nat.divLarge` (`fn + 0x418`, return `retL = fn + 0x41d` at `RSP - 240`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatDiv

/-- `divLarge`'s return site in `nat.div` (`fn + 0x41d`) -/
abbrev retL : Nat := 0x5ee33d
/-- `divLarge`'s entry -/
abbrev divLE : Nat := 0x5ee920

theorem divLE_eq : segAddr Extracted.program DivLarge.fn = divLE := by decide

/-- `divLarge`'s window (at `RSP - 240`) lies inside `nat.div`'s -/
theorem winX {s X : State} (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240) (hb : 41512 ≤ (s.regs 4).toNat)
    {a n : Nat} (h : Outside a n (win s 41512 112)) : Outside a n (win X 41272 112) := by
  simp only [win, outside_cons, outside_nil, and_true] at h ⊢
  rw [hspn]
  generalize (s.regs 4).toNat = t at hb h ⊢
  rw [show t - 240 - 41272 = t - 41512 by omega, show t - 240 + 112 = t - 128 by omega]
  omega

/-- the state at `divLarge`'s entry -/
structure AtL (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s X : State) : Prop where
  pc : X.rip = BitVec.ofNat 64 divLE
  sp : X.regs 4 = s.regs 4 - 240#64
  r5 : X.regs 5 = s.regs 4 - 8#64
  r14 : X.regs 14 = s.regs 14
  fs : X.fsBase = s.fsBase
  x15 : X.xmm 15 = 0#128
  df : X.df = false
  a0 : X.regs 0 = BitVec.ofNat 64 zp
  a3 : X.regs 3 = BitVec.ofNat 64 zl
  a1 : X.regs 1 = BitVec.ofNat 64 zc
  a7 : X.regs 7 = BitVec.ofNat 64 st
  a6 : X.regs 6 = BitVec.ofNat 64 z2
  a8 : X.regs 8 = BitVec.ofNat 64 z2l
  a9 : X.regs 9 = BitVec.ofNat 64 z2c
  rc : X.mem.readLE ((s.regs 4).toNat - 240) 8 = retL
  mf : MemFrame s.mem X.mem (win s 41512 112)
  reg : X.mem.regions = s.mem.regions
  ra : X.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : X.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  by0 : X.mem.readLE ((s.regs 4).toNat - 122) 1 = 0
  i0 : X.mem.readLE ((s.regs 4).toNat - 232) 8 = u
  i1 : X.mem.readLE ((s.regs 4).toNat - 224) 8 = ul
  i2 : X.mem.readLE ((s.regs 4).toNat - 216) 8 = uc
  i3 : X.mem.readLE ((s.regs 4).toNat - 208) 8 = v
  i4 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = vl
  i5 : X.mem.readLE ((s.regs 4).toNat - 192) 8 = vc

end FvModexp.Amd64.NatDiv
