import FvModexp.Proofs.Amd64.NatQ.SqrSCC

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/NatSqr.lean — TIGHT COSTS] `z.sqr(stk, x)` (go-bigmodexpfix
natmul.go:73), amd64: the summary

`ens`: the `Ensures` of CONVENTIONS §3 on `LibSqr` (= `nat.sqr`, `karatsubaSqr`, `basicSqr`, `basicMul`,
`(*stack).nat`, `(*Int).Add/Sub`, `addTo`, the asm leaves; none of `nat.sqr`'s callers), from the SCC (`SqrSCC.scc`,
member `(false, ·)`); `sum`: `ens` as a callee summary. Pre `SPre` / post `SPost` (`SqrDefs`; amortised stack budget
`sqrCQ (len x) + stkR H`, the stack comes back in the `StackBackL` form).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

/-- **`nat.sqr`** (amd64): `z.sqr(stk, x)` returns `X²` normalised, in `z`'s array when it is large enough and not
`x`'s alias (writing only `z[0:2·len x]`), else in a fresh array; the stack comes back (`StackBackL`); no panic, no
fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, st, xp, xl, xc]
      (SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)
      (SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat) := by
  janus64_ensures_old [FvModexp.Amd64.Q.NatSqr.SPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.NatAdd.wordT, FvModexp.NatLive, FvModexp.Amd64.Q.NatSqr.guard, FvModexp.Amd64.Q.NatSqr.tls, FvModexp.Amd64.Q.NatSqr.StkSep, FvModexp.Amd64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.stkR, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.Amd64.Q.BasicSqr.freeP, FvModexp.Amd64.Q.BasicSqr.freeN, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.stkRes, FvModexp.potK]
  rw [show names = LibSqr.names from rfl, ← LibSqr.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  have hS := scc (H := H) impl hap R hmk hgr hmc hmv hwb (false, ⟨b, L, W, zp, zl, zc, st, xp, xl, xc⟩)
  refine Summary.returns hS hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5,
      h_a6⟩, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hgr hmc hmv hwb H b L W zp zl zc st xp xl xc)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.Q.NatSqr
