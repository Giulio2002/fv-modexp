import FvModexp.Proofs.Amd64.Exp.P2W4C

set_option autoImplicit false

/-!
# **`nat.expNNPowerOfTwoWindowSize4`** (amd64): `ens` / `sum` (agent divmc s77, port of divmc s75; amd64 twin of agent infra's
`Arm64.P2W4E` / `P2W4EC`)

`ens`: the `Ensures` form of `fullC` on the restricted program `LibW.names` (callers outside it), from the live
runtime contracts of the whole extraction (moved to `LibW.program.link impl` by `of_codeIn`); arguments `z = (AX, BX,
CX)`, `stk = DI`, `x = (SI, R8, R9)`, `logM = R10`, `y` on the stack (`NHyp.StkArg s 0`). `sum`: `ens` as a callee
summary in a caller whose program keeps `ms ⊇ LibW.names`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open Janus.Contracts.EqHashModel (CodeIn64)

def names : List String := LibW.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`expNNPowerOfTwoWindowSize4`** (amd64): returns `x^y mod 2^logM` for odd `x`, `y > 0` (see `PreC`) -/
theorem ens {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41512 + 0x300 ≤ stk) (hk1 : P2Pre.K kc + 0x300 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x300)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 lm]
      (fun s => NHyp.StkArg s 0 yp yl yc ∧ PreC R b L stk (costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧
        EX xp xl s)
      (fun s s' => NHyp.CPostR R b L stk 0x60 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
        (costB (stLen s.mem st) yl lm) s s') := by
  janus64_ensures_old [FvModexp.Amd64.NHyp.StkArg, FvModexp.Amd64.P2W4.PreC, FvModexp.stLen, FvModexp.Amd64.P2W4.EX, FvModexp.Amd64.NHyp.CPre, FvModexp.natVal, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.win, FvModexp.Amd64.ExpHyp.stWs, FvModexp.Amd64.NHyp.StkApart, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.stkWs, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hgrL : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R := by
    rw [show grE = cA "runtime.growslice" by decide]; exact StackNatX.GrowsliceLiveContract64.of_codeIn' hc hgr
  have hmcL : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R := by
    rw [show mcE = cA "runtime.memclrNoHeapPointers" by decide]; exact MemclrNoHeapPointersLive64.of_codeIn hc hmc
  have hmvL : MemmoveLive64 (LibW.program.link impl) mvE 4096 R := by
    rw [show mvE = cA "runtime.memmove" by decide]; exact MemmoveLive64.of_codeIn hc hmv
  have hmkL : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R := by
    rw [show mkE = cA "runtime.makeslice" by decide]; exact MakesliceLiveContract64.of_codeIn hc hmk
  have hnoL : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R := by
    rw [show noE = cA "runtime.newobject" by decide]; exact NewobjectLiveContract64.of_codeIn hc hno
  have hwbL : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2 := by
    rw [show wbE = cA "runtime.gcWriteBarrier2" by decide]; exact WbLiveContract64.of_codeIn hc hwb
  have hS := fullC hap hns hnf hnfP hgrL hmcL hmvL hmkL hnoL hwbL hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT haT
    b L stk hk0 hk1 hk2 zp zl zc st xp xl xc yp yl yc lm hzp hxc
  rw [show names = LibW.names from rfl, ← LibW.eq_only, show segAddr Extracted.program fn = fnE by decide]
  intro ret hret s hs ⟨hy, hP, hX⟩
  janus64_intro hs
  refine Summary.returns hS hret h_rip (by rw [retAddrOf, h_ret])
    ⟨h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6, h_a7, hy, h_x15, h_df, hP, hX, by rw [h_ret]; exact hret.user⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ LibW.names` -/
def sum {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41512 + 0x300 ≤ stk) (hk1 : P2Pre.K kc + 0x300 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x300)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (ms : List String) (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT
    haT b L stk hk0 hk1 hk2 zp zl zc st xp xl xc yp yl yc lm hzp hxc)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.P2W4
