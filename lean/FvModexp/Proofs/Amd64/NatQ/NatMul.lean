import FvModexp.Proofs.Amd64.NatQ.MulSCC
import FvModexp.Proofs.Amd64.NatQ.MulHypQE

set_option autoImplicit false

/-!
# [amd64 port (divmc s54) of the Q-form Arm64/NatQ/NatMul.lean — TIGHT COSTS] `z.mul(stk, x, y)` (go-bigmodexpfix natmul.go:16), amd64: the summary

`ens`: the `Ensures` of CONVENTIONS §3 on `LibMul` (= `nat.mul`, `karatsuba`, `(*Int).mul`, `basicMul`, `addTo`,
`(*stack).nat`, `(*Int).Add/Sub`, the asm leaves; none of `nat.mul`'s callers), from the SCC (`MulSCC.scc`, member
`(.mul, ·)`): register arguments `z = (AX, BX, CX)`, `stk = DI`, `x = (SI, R8, R9)`; `y` on the stack at
`RSP + 8 / + 16 / + 24` (Go ABIInternal), bound by the pre. Pre `MPre` / post `MPost` (`MulDefs`; the stack comes back in
the `StackBackL` form, the `Exact` clause states the in-place write). `hypQE`: `ens` in asm's shape
`Q.DivRec.MulHypQE` (the amd64 drs's `nat.mul` premise). `sum`: `ens` as a callee summary.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

/-- **`nat.mul`** (amd64): `z.mul(stk, x, y)` returns `X·Y` normalised, in `z`'s array when it is large enough and not
an operand's alias (writing only `z[0:len x + len y]`), else in a fresh array; the stack comes back (`StackBackL`); no
panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) (yp yl yc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, st, xp, xl, xc]
      (fun s => s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl ∧
        s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc ∧
        MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp yl yc s)
      (fun s s' => MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp yl yc s s') := by
  janus64_ensures_old [FvModexp.Amd64.Q.NatMul.MPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.Q.NatMul.Ops, FvModexp.Amd64.Q.NatSqr.tls, FvModexp.Amd64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.stkR, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.Amd64.Q.BasicSqr.ws, FvModexp.Amd64.Q.NatSqr.StkSep, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.Q.NatSqr.guard, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.Q.BasicSqr.freeP, FvModexp.Amd64.Q.BasicSqr.freeN, FvModexp.Amd64.StackNat.wbA, FvModexp.stkRes, FvModexp.potK, FvModexp.stkWs]
  rw [show names = LibMul.names from rfl, ← LibMul.eq_only]
  intro ret hret s hs ⟨hy1, hy2, hy3, hpre⟩
  janus64_intro hs
  have e7 : (BitVec.ofNat 64 yp).toNat = yp := by
    rw [BitVec.toNat_ofNat, ← hy1]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Arm64.Memory.readLE_lt _ _ _) (by decide))
  have e8 : (BitVec.ofNat 64 yl).toNat = yl := by
    rw [BitVec.toNat_ofNat, ← hy2]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Arm64.Memory.readLE_lt _ _ _) (by decide))
  have e9 : (BitVec.ofNat 64 yc).toNat = yc := by
    rw [BitVec.toNat_ofNat, ← hy3]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Arm64.Memory.readLE_lt _ _ _) (by decide))
  have hS := scc (H := H) impl hap R hmk hgr hmc hmv hwb
    (.mul, ⟨b, L, W, zp, zl, zc, st, xp, xl, xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc⟩)
  refine Summary.returns hS hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5,
      h_a6, by rw [e7]; exact hy1, by rw [e8]; exact hy2, by rw [e9]; exact hy3⟩, ?_⟩
    fun s' ⟨⟨k1, k2, k3, k4⟩, hq⟩ => ⟨⟨k1, k2, k3, k4⟩, ?_⟩
  · show MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat (BitVec.ofNat 64 yp).toNat
      (BitVec.ofNat 64 yl).toNat (BitVec.ofNat 64 yc).toNat s
    rw [e7, e8, e9]; exact hpre
  · have hq' : MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat (BitVec.ofNat 64 yp).toNat
        (BitVec.ofNat 64 yl).toNat (BitVec.ofNat 64 yc).toNat s s' := hq
    rw [e7, e8, e9] at hq'; exact hq'

/-- **`nat.mul` in asm's `Q.DivRec.MulHypQE` shape** (amd64 drs premise; any window `W`) -/
theorem hypQE (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) (W : Nat) :
    Q.DivRec.MulHypQE impl R names W :=
  fun H b L z zl zc st x xl xc yp yl yc => ens impl hap R hmk hgr hmc hmv hwb H b L W z zl zc st x xl xc yp yl yc

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) (yp yl yc : Nat)
    (ms : List String) (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hgr hmc hmv hwb H b L W zp zl zc st xp xl xc yp yl yc)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.Q.NatMul
