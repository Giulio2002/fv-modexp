import FvModexp.Proofs.Arm64.Nat.MulRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.mul` (arm64), `make_alloc`: the state at the `makeslice` call `0x1baf48`

`AA s S …`: after the prologue and the alias / capacity tests (natmul.go:31-35) every allocating path reaches `makeslice`'s entry
(CALL at `0x1baf48`, return `0x1baf4c`) with `R0 = Word`'s type descriptor, `R1 = m + n`, `R2 = m + n + 4`, the spills `120(SP') = m + n`,
`96(SP') = m + n + 4`, `288..336(SP') = stk, x, y` (`SP' = SP - 256`), memory changed in the window only.
Split so the alias tests (MulMakeA1) and the call (MulMakeA2) are run separately (MulMakeA was 286 s / 8.0 GB).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

/-- see the module doc -/
structure AA (s S : State) (W : Nat) (st xp xl xc yp yl yc : BitVec 64) : Prop where
  pc : S.pc = BitVec.ofNat 64 (cA "runtime.makeslice")
  r30 : S.regs 30 = BitVec.ofNat 64 0x1baf4c
  r0 : S.regs 0 = BitVec.ofNat 64 NatAdd.wordT
  r1 : S.regs 1 = BitVec.ofNat 64 (xl.toNat + yl.toNat)
  r2 : S.regs 2 = BitVec.ofNat 64 (xl.toNat + yl.toNat + 4)
  sp : S.sp = s.sp - 256#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 264#64
  x18 : S.regs 18 = s.regs 18
  mlr : S.mem.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat
  mfp : S.mem.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat
  m120 : S.mem.readLE (s.sp.toNat - 136) 8 = xl.toNat + yl.toNat
  m96 : S.mem.readLE (s.sp.toNat - 160) 8 = xl.toNat + yl.toNat + 4
  m288 : S.mem.readLE (s.sp.toNat + 32) 8 = st.toNat
  m296 : S.mem.readLE (s.sp.toNat + 40) 8 = xp.toNat
  m304 : S.mem.readLE (s.sp.toNat + 48) 8 = xl.toNat
  m312 : S.mem.readLE (s.sp.toNat + 56) 8 = xc.toNat
  m320 : S.mem.readLE (s.sp.toNat + 64) 8 = yp.toNat
  m328 : S.mem.readLE (s.sp.toNat + 72) 8 = yl.toNat
  m336 : S.mem.readLE (s.sp.toNat + 80) 8 = yc.toNat
  F : MemFrame s.mem S.mem (winA s W 88)
  reg : S.mem.regions = s.mem.regions

end FvModexp.Arm64.NatMul
