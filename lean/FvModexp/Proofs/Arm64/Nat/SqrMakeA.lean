import FvModexp.Proofs.Arm64.Nat.SqrMakeA1
import FvModexp.Proofs.Arm64.Nat.SqrMakeA2

set_option autoImplicit false

/-!
# `nat.sqr` (arm64), `n ≥ 2`, `make_alloc`: `if alias(z, x) { z = nil }; z = z.make(2n)` (natmul.go:85-88) when `z` is
too small or `x`'s alias → `makeslice(Word, 2n, 2n + 4)` → the join `+0x104`

Composition of `alloc_head` (SqrMakeA1: entry → the `makeslice` call) and `alloc_call` (SqrMakeA2: the call → the join).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem make_alloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s Q :=
  alloc_head impl R b L W zp zl zc st xp xl xc s hpc h0 h1 h2 h3 h4 h5 h6 hpre hx hz Q
    fun S hA => alloc_call impl R hmk b L W zp zl zc st xp xl xc s S hA hpre hx hz Q hK

end FvModexp.Arm64.NatSqr
