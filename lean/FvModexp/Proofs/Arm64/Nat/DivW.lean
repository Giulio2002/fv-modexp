import FvModexp.Proofs.Arm64.Nat.DivWGen
import FvModexp.Proofs.Arm64.Nat.DivWSetE
import FvModexp.Proofs.Arm64.Nat.DivWZero

/-!
# `nat.divW` (go-bigmodexpfix natdiv.go:550), arm64: the summary

`full`: the `Summary` at the entry over all paths (`m = 0`: `zeroPath` / `setZero`; `y = 1`: `setPath`; else
`genReuse` / `genAlloc`); `ens`: the `Ensures` of CONVENTIONS §3 on `(Extracted.program.onlySegments names).link impl`;
`sum`: `ens` as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDivW.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = y ∧
        Pre R b L zp zc xp xl y s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibDivW.program.link impl) := by
    rw [LibDivW.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibDivW.names
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  have hy0 : y.toNat ≠ 0 := hpre.2.2.1
  by_cases hy1 : y.toNat = 1
  · have hy : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hy1)
    subst hy
    by_cases hx0 : xl.toNat = 0
    · have hx : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
      subst hx
      exact setZero impl R hmv' b L zp zl zc xp xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre
    · exact setPath impl R hmk' hmv' b L zp zl zc xp xl xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega) hpre
  by_cases hx0 : xl.toNat = 0
  · have hx : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
    subst hx
    exact zeroPath impl b R L zp zl zc xp xc y s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hy0 hy1 hpre
  by_cases hz : xl.toNat ≤ zc.toNat
  · exact genReuse impl hap R b L zp zl zc xp xl xc y s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega) hy0 hy1 hz hpre
  · exact genAlloc impl hap R hmk' b L zp zl zc xp xl xc y s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega) hy0 hy1
      (by omega) hpre

/-- **`nat.divW`** (arm64): `z.divW(x, y)` (`y ≠ 0`, `x` normalised) returns a normalised nat holding `X / y`, in
`z`'s array (`zc ≥ len x`) or a fresh one, and `X % y`; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (Pre R b L zp zc xp xl y) (Post R b L zp zc xp xl y) := by
  rw [show names = LibDivW.names from rfl, ← LibDivW.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk hmv b L zp zl zc xp xl xc y) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv b L zp zl zc xp xl xc y) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.DivW
