import FvModexp.Proofs.Amd64.Nat.SqrMakeA1
import FvModexp.Proofs.Amd64.Nat.SqrMakeA2

set_option autoImplicit false

/-!
# `nat.sqr` (amd64), `n ≥ 2`, `make_alloc`: `if alias(z, x) { z = nil }; z = z.make(2n)` (natmul.go:85-88) when `z` is
too small or `x`'s alias → `makeslice(Word, 2n, 2n + 4)` → the join `0x5f1140`

Composition of `alloc_head` (SqrMakeA1: entry → the `makeslice` call) and `alloc_call` (SqrMakeA2: the call → the join).
Twin of the arm64 module (divmc s32).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSqr

theorem make_alloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0fe0)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) s Q :=
  alloc_head impl R b L W zp zl zc st xp xl xc s hpc h0 h3 h1 h7 h6 h8 h9 hpre hx hz Q
    fun S hA => alloc_call impl R hmk b L W zp zl zc st xp xl xc s S hA hpre hx hz Q hK

end FvModexp.Amd64.NatSqr
