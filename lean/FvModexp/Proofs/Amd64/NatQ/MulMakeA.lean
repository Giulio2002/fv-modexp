import FvModexp.Proofs.Amd64.NatQ.MulMakeA2

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulMakeA.lean — TIGHT COSTS] `nat.mul` (amd64): `z.make(m + n)` by `makeslice`

Composition of `alloc_head` (MulMakeA1: entry → the `makeslice` call) and `alloc_call` (MulMakeA2: the call → the join).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem make_alloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibMul.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0840)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hy1 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat) (hy2 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat)
    (hy3 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hyl2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s Q :=
  alloc_head impl R b L W zp zl zc st xp xl xc yp yl yc s hpc h0 h3 h1 h7 h6 h8 h9 hy1 hy2 hy3 hpre hyl2 hyx hz Q
    fun S hA => alloc_call impl R hmk b L W zp zl zc st xp xl xc yp yl yc s S hA hpre hyl2 hyx hz Q hK

end FvModexp.Amd64.Q.NatMul
