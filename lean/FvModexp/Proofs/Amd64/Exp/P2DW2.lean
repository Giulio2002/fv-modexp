import FvModexp.Proofs.Amd64.Exp.P2DWS
import FvModexp.Proofs.Amd64.Exp.P2W2C

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): divmc's `P2W2.fullC` as a window summary `WSum` (agent asm s68)

`wsum2`: `expNNPowerOfTwoWindowSize2`'s summary (`P2W2.fullC`, agent divmc s74) in the shape `P2D.WSum` consumed by the
odd path of `expNNPowerOfTwo` (entry `P2W2.fnE`, stack need `max (41512 + 0x1d8) (P2Pre.K kc + 0x1d8)`, budget
`P2W2.costB`). The two statements differ only in the packaging (`WPre` = `Regs ∧ (X15, DF, zp) ∧ PreC`'s conjuncts with
`0 < X` extra ∧ `len x ≤ cap x < 2^40` ∧ `EX` ∧ the return-address bound); the post is the same `PostD`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

/-- **the size-2 window summary** in the `WSum` shape -/
theorem wsum2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains P2W2.fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) P2W2.grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) P2W2.mcE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) P2W2.mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) P2W2.mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) P2W2.noE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) P2W2.wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88) :
    WSum impl R P2W2.fnE (max (41512 + 0x1d8) (P2Pre.K kc + 0x1d8)) P2W2.costB := by
  intro b L stk zp zl zc st xp xl xc yp yl yc lm hk hk2 s hpc hpre
  obtain ⟨⟨h0, h3, h1, h7, h6, h8, h9, h10, hy⟩, ⟨hx15, hdf, hzp⟩, hC, -, hXo, hY, hl2, hl, hst, hone, -, hxc,
    hEX, hr47⟩ := hpre
  exact P2W2.fullC hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT
    b L stk (by omega) (by omega) (by omega) zp zl zc st xp xl xc yp yl yc lm hzp (by omega) s hpc
    ⟨h0, h3, h1, h7, h6, h8, h9, h10, hy, hx15, hdf, ⟨hC, hXo, hY, hl2, hl, hst, hone⟩, hEX, hr47⟩

end FvModexp.Amd64.P2D
