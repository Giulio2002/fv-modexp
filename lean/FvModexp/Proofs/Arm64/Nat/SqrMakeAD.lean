import FvModexp.Proofs.Arm64.Nat.SqrRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.sqr` (arm64), `make_alloc`: the state at the `makeslice` call `0x1bb500`

`AA s S …`: after the prologue and the alias / capacity test (natmul.go:85-88) every allocating path reaches `makeslice`'s
entry (CALL at `0x1bb500`, return `0x1bb504`) with `R0 = Word`'s type descriptor, `R1 = 2n`, `R2 = 2n + 4`, the spills
`96(SP') = 2n`, `88(SP') = 2n + 4`, `208..232(SP') = stk, x` (`SP' = SP - 176`), memory changed in the window only.
Split (as MulMakeAD) so the alias tests (SqrMakeA1) and the call (SqrMakeA2) are run separately (SqrMake was 194 s).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- see the module doc -/
structure AA (s S : State) (W : Nat) (st xp xl xc : BitVec 64) : Prop where
  pc : S.pc = BitVec.ofNat 64 (cA "runtime.makeslice")
  r30 : S.regs 30 = BitVec.ofNat 64 0x1bb504
  r0 : S.regs 0 = BitVec.ofNat 64 NatAdd.wordT
  r1 : S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat)
  r2 : S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat + 4)
  sp : S.sp = s.sp - 176#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 184#64
  x18 : S.regs 18 = s.regs 18
  mlr : S.mem.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat
  mfp : S.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat
  m96 : S.mem.readLE (s.sp.toNat - 80) 8 = 2 * xl.toNat
  m88 : S.mem.readLE (s.sp.toNat - 88) 8 = 2 * xl.toNat + 4
  m208 : S.mem.readLE (s.sp.toNat + 32) 8 = st.toNat
  m216 : S.mem.readLE (s.sp.toNat + 40) 8 = xp.toNat
  m224 : S.mem.readLE (s.sp.toNat + 48) 8 = xl.toNat
  m232 : S.mem.readLE (s.sp.toNat + 56) 8 = xc.toNat
  F : MemFrame s.mem S.mem (winA s W 64)
  reg : S.mem.regions = s.mem.regions

end FvModexp.Arm64.NatSqr
