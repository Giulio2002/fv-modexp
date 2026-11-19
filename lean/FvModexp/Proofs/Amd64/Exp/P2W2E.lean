import FvModexp.Proofs.Amd64.Exp.P2W2C
import FvModexp.Proofs.Amd64.Exp.SetRetWinX

set_option autoImplicit false

/-!
# **`nat.expNNPowerOfTwoWindowSize2`** (amd64): `ens` / `sum` (agent divmc s75; amd64 twin of agent infra's
`Arm64.P2W2E` / `P2W2EC`)

`ens`: the `Ensures` form of `fullC` on the restricted program `LibW.names` (callers outside it), from the live
runtime contracts of the whole extraction (moved to `LibW.program.link impl` by `of_codeIn`); arguments `z = (AX, BX,
CX)`, `stk = DI`, `x = (SI, R8, R9)`, `logM = R10`, `y` on the stack (`NHyp.StkArg s 0`). `sum`: `ens` as a callee
summary in a caller whose program keeps `ms ⊇ LibW.names`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open Janus.Contracts.EqHashModel (CodeIn64)

def names : List String := LibW.names

/-- `ens`'s precondition survives installing the return address (Janus v0.4.0 `hinv`; top s54: `janus64_ensures_old`'s closer
cannot see the `natOne` word's apartness under the `∃ op`; by the frame lemmas `SetRetWin` / `SetRetWinX` instead) -/
theorem pre_setRet {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk zp zl zc st xp xl yp yl yc lm : Nat} {s : State}
    (ret : Nat) (hp : NHyp.StkArg s 0 yp yl yc ∧ PreC R b L stk (costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧
      EX xp xl s) :
    NHyp.StkArg (s.setRet ret) 0 yp yl yc ∧
      PreC R b L stk (costB (stLen (s.setRet ret).mem st) yl lm) zp zl zc st xp xl yp yl lm (s.setRet ret) ∧
      EX xp xl (s.setRet ret) := by
  have hab : 8 ≤ 0x60 := by decide
  obtain ⟨⟨y1, y2, y3⟩, ⟨hC, hxv, hyv, hl1, hl2, hst, hO⟩, x1, x2, x3⟩ := hp
  have h10 : Outside st 24 (win s stk 0x60) := hC.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hl, -⟩ := SetRetWin.stHdr (ret := ret) hab h10
  have hrx := (hC.2.2.2.2.2.2.2.1 xp xl (by simp)).1
  have hry := (hC.2.2.2.2.2.2.2.1 yp yl (by simp)).1
  obtain ⟨hone, hO'⟩ := SetRetWin.natOne (ret := ret) hab h10 hO
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, hl1, hl2, hst, hO'⟩, x1, ?_, ?_⟩
  · exact (readLE_setRet_of_disjoint (s := s) (ret := ret) (a := (s.regs 4).toNat + 0 + 8) (n := 8)
      (Or.inr (by omega))).trans y1
  · exact (readLE_setRet_of_disjoint (s := s) (ret := ret) (a := (s.regs 4).toNat + 0 + 16) (n := 8)
      (Or.inr (by omega))).trans y2
  · exact (readLE_setRet_of_disjoint (s := s) (ret := ret) (a := (s.regs 4).toNat + 0 + 24) (n := 8)
      (Or.inr (by omega))).trans y3
  · rw [hl]; exact SetRetWin.cpre hab hC
  · show (s.setRet ret).mem.readLE xp (8 * xl) % 2 = 1; rw [SetRetWin.rd hab hrx.2.2.2.2]; exact hxv
  · show 0 < (s.setRet ret).mem.readLE yp (8 * yl); rw [SetRetWin.rd hab hry.2.2.2.2]; exact hyv
  · rw [hone]; exact x2
  · rw [setRet_accessible]; exact x3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`expNNPowerOfTwoWindowSize2`** (amd64): returns `x^y mod 2^logM` for odd `x`, `y > 0` (see `PreC`) -/
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
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41512 + 0x1d8 ≤ stk) (hk1 : P2Pre.K kc + 0x1d8 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x1d8)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 lm]
      (fun s => NHyp.StkArg s 0 yp yl yc ∧ PreC R b L stk (costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧
        EX xp xl s)
      (fun s s' => NHyp.CPostR R b L stk 0x60 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
        (costB (stLen s.mem st) yl lm) s s') := by
  refine Ensures.of_old (fun s ret _ _ hp => pre_setRet ret hp) ?_
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
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41512 + 0x1d8 ≤ stk) (hk1 : P2Pre.K kc + 0x1d8 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x1d8)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (ms : List String) (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens hap hns hnf hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr hkT
    haT b L stk hk0 hk1 hk2 zp zl zc st xp xl xc yp yl yc lm hzp hxc)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.P2W2
