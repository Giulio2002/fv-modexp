import FvModexp.Proofs.Arm64.NatQ.MulSCC

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/NatMul.lean — TIGHT COSTS, divmc s34] `z.mul(stk, x, y)` (go-bigmodexpfix natmul.go:16), arm64: the summary

`ens`: the `Ensures` of CONVENTIONS §3 on `LibMul` (= `nat.mul`, `karatsuba`, `(*Int).mul`, `basicMul`, `addTo`,
`(*stack).nat`, `(*Int).Add/Sub`, the asm leaves; none of `nat.mul`'s callers), from the SCC (`MulSCC.scc`, member
`(.mul, ·)`); `sum`: `ens` as a callee summary. Pre `MPre` / post `MPost` (`MulDefs`; the stack comes back in the
`StackBackL` form, the `Exact` clause states the in-place write). (Structure as this repo's `NatSqr.ens`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

/-- **`nat.mul`** (arm64): `z.mul(stk, x, y)` returns `X·Y` normalised, in `z`'s array when it is large enough and not
an operand's alias (writing only `z[0:len x + len y]`), else in a fresh array; the stack comes back (`StackBackL`); no
panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, st, xp, xl, xc, yp, yl, yc]
      (MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat)
      (MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat) := by
  janus_ensures_old [FvModexp.Arm64.Q.NatMul.MPre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.NatAdd.wordT, FvModexp.Arm64.Q.NatMul.Ops, FvModexp.Arm64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.stkR, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.RunIface.wbA, FvModexp.Arm64.Q.BasicSqr.ws, FvModexp.Arm64.Q.NatSqr.StkSep, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Arm64.Q.NatSqr.guard, FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.Q.BasicSqr.freeP, FvModexp.Arm64.Q.BasicSqr.freeN, FvModexp.Arm64.StackNat.wbA, FvModexp.stkRes, FvModexp.potK, FvModexp.stkWs]
  rw [show names = LibMul.names from rfl, ← LibMul.eq_only, entry_mul]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  have hS := scc (H := H) impl hap R hmk hgr hmc hmv hwb (.mul, ⟨b, L, W, zp, zl, zc, st, xp, xl, xc, yp, yl, yc⟩)
  refine Summary.returns hS hret h_pc h_lr
    ⟨⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, h_x9⟩, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc yp yl yc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hgr hmc hmv hwb H b L W zp zl zc st xp xl xc yp yl yc)
    (noExit_restrict hap names) (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.Q.NatMul
