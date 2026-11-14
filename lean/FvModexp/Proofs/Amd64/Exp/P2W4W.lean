import FvModexp.Proofs.Amd64.Exp.P2W4C
import FvModexp.Proofs.Amd64.Exp.P2DWS

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64) as asm's `P2D.WSum` (agent divmc s78; window-4 twin of asm's `P2D.wsum2`)

`P2W4.wsum`: `fullC` (agent divmc s77) in the shape `P2D.WSum` consumed by the odd path of `expNNPowerOfTwo`
(entry `fnE`, stack need `max (41512 + 0x300) (P2Pre.K kc + 0x300)`, budget `costB`), using asm's amended `WPre`
(the `X15 = 0 ∧ DF clear ∧ zp < 2^64` conjunct) and `stk ≤ 2^20`. Post `PostD` unchanged.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- **the size-4 window summary** in the `WSum` shape -/
theorem wsum {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88) :
    P2D.WSum impl R fnE (max (41512 + 0x300) (P2Pre.K kc + 0x300)) costB := by
  intro b L stk zp zl zc st xp xl xc yp yl yc lm hk hk2 s hpc hpre
  obtain ⟨⟨h0, h3, h1, h7, h6, h8, h9, h10, hy⟩, ⟨hx15, hdf, hzp⟩, hC, -, hXo, hY, hl2, hl, hst, hone, -, hxc,
    hEX, hr47⟩ := hpre
  exact fullC hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT
    b L stk (by omega) (by omega) (by omega) zp zl zc st xp xl xc yp yl yc lm hzp (by omega) s hpc
    ⟨h0, h3, h1, h7, h6, h8, h9, h10, hy, hx15, hdf, ⟨hC, hXo, hY, hl2, hl, hst, hone⟩, hEX, hr47⟩

end FvModexp.Amd64.P2W4
