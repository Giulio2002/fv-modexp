import FvModexp.Proofs.Arm64.Nat.MulMakeA1
import FvModexp.Proofs.Arm64.Nat.MulMakeA2

set_option autoImplicit false

/-!
# `nat.mul` (arm64), `m ≥ n ≥ 2`, `make_alloc`: `if alias(z, x) || alias(z, y) { z = nil }; z = z.make(m + n)`
(natmul.go:31-35) when `z` is too small or an operand's alias → `makeslice(Word, m + n, m + n + 4)` → the join `0x1baf70`

Composition of `alloc_head` (MulMakeA1: entry → the `makeslice` call, every allocating path) and `alloc_call` (MulMakeA2:
the call → the join). (`make_reuse`: MulMakeR.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

theorem make_alloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMul.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s Q :=
  alloc_head impl R b L W zp zl zc st xp xl xc yp yl yc s hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hpre hy2 hyx hz Q
    fun S hA => alloc_call impl R hmk b L W zp zl zc st xp xl xc yp yl yc s S hA hpre hy2 hyx hz Q hK

end FvModexp.Arm64.NatMul
