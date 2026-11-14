import FvModexp.Proofs.Amd64.Exp.P2W2C
import FvModexp.Proofs.Amd64.Exp.P2DWS

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64) in asm's `P2D` window-summary shape (agent divmc s75)

`wsumX`: `fullC` as a summary with pre `P2D.WPre … ∧ X15 = 0 ∧ DF clear ∧ zp < 2^64` (window `stk ≤ 2^20`) and post
`P2D.PostD` at budget `costB`. The three extra conjuncts are what `fullC` needs beyond `WPre` (NOTES-conventions
"[divmc s75 → asm] P2D WSum/WPre vs fullC"); once `WPre` carries them, `P2D.WSum impl R fnE kW costB` follows directly.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

set_option maxRecDepth 20000 in
theorem wsumX {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    {kW : Nat} (hkW0 : 41512 + 0x1d8 ≤ kW) (hkW1 : P2Pre.K kc + 0x1d8 ≤ kW)
    (b : Nat) (L : List (Nat × Nat)) (stk zp zl zc st xp xl xc yp yl yc lm : Nat) (hk : kW ≤ stk)
    (hk2 : stk ≤ 2 ^ 20) :
    Summary (LibW.program.link impl) fnE
      (fun s => P2D.WPre R b L stk 0x60 (costB (stLen s.mem st) yl lm) zp zl zc st xp xl xc yp yl yc lm s ∧
        s.xmm 15 = 0 ∧ s.df = false ∧ zp < 2 ^ 64)
      (fun s s' => P2D.PostD R b L stk 0x60 (costB (stLen s.mem st) yl lm) zp zc st
        (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s s') := by
  rintro s hpc ⟨⟨⟨h0, h3, h1, h7, h6, h8, h9, h10, hy⟩, hC, -, hX, hY, hl2, hl, hst, hop, -, hxc, hEX, hr47⟩, hx15,
    hdf, hzp⟩
  exact fullC hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT b L stk
    (by omega) (by omega) (by omega) zp zl zc st xp xl xc yp yl yc lm hzp (by omega) s hpc
    ⟨h0, h3, h1, h7, h6, h8, h9, h10, hy, hx15, hdf, ⟨hC, hX, hY, hl2, hl, hst, hop⟩, hEX, hr47⟩

end FvModexp.Amd64.P2W2
