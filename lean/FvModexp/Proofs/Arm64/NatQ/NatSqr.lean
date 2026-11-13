import FvModexp.Proofs.Arm64.NatQ.SqrSCC

/-!
# [Q-form copy of Arm64/Nat/NatSqr.lean — TIGHT COSTS, divmc s34] `z.sqr(stk, x)` (go-bigmodexpfix natmul.go:73), arm64: the summary

`ens`: the `Ensures` of CONVENTIONS §3 on `LibSqr` (= `nat.sqr`, `karatsubaSqr`, `basicSqr`, `basicMul`, `(*stack).nat`,
`(*Int).Add/Sub`, `addTo`, the asm leaves; none of `nat.sqr`'s callers), from the SCC (`SqrSCC.scc`, member
`(false, ·)`); `sum`: `ens` as a callee summary. Pre `SPre` / post `SPost` (`SqrDefs`; the stack comes back in the
`StackBackL` form).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

/-- **`nat.sqr`** (arm64): `z.sqr(stk, x)` returns `X²` normalised, in `z`'s array when it is large enough and not
`x`'s alias (writing only `z[0:2·len x]`), else in a fresh array; the stack comes back (`StackBackL`); no panic, no
fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, st, xp, xl, xc]
      (SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)
      (SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat) := by
  rw [show names = LibSqr.names from rfl, ← LibSqr.eq_only, entry_sqr]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  have hS := scc (H := H) impl hap R hmk hgr hmc hmv hwb (false, ⟨b, L, W, zp, zl, zc, st, xp, xl, xc⟩)
  refine Summary.returns hS hret h_pc h_lr ⟨⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6⟩, hpre⟩
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
    (H b : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hgr hmc hmv hwb H b L W zp zl zc st xp xl xc)
    (noExit_restrict hap names) (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.Q.NatSqr
