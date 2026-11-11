import FvModexp.Proofs.Amd64.Nat.DivWGen
import FvModexp.Proofs.Amd64.Nat.DivWSetE
import FvModexp.Proofs.Amd64.Nat.DivWZero

/-!
# `nat.divW` (go-bigmodexpfix natdiv.go:550), amd64: the summary (`full`, `ens`, `sum`; see the arm64 twin)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDivW.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = y ∧ Pre R b L zp zc xp xl y s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc xp xl y s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibDivW.program.link impl) := by
    rw [LibDivW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDivW.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  have hy0 : y.toNat ≠ 0 := hpre.2.2.1
  by_cases hy1 : y.toNat = 1
  · have hy : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hy1)
    subst hy
    by_cases hx0 : xl.toNat = 0
    · have hx : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
      subst hx
      exact setZero impl R hmv' b L zp zl zc xp xc s ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ hpre
    · exact setPath impl R hmk' hmv' b L zp zl zc xp xl xc s ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩
        (by omega) hpre
  have he : Entry s zp zl zc xp xl xc y := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩
  by_cases hx0 : xl.toNat = 0
  · have hx : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
    subst hx
    exact zeroPath impl b R L zp zl zc xp xc y s he hy0 hy1 hpre
  by_cases hz : xl.toNat ≤ zc.toNat
  · exact genReuse impl hap R b L zp zl zc xp xl xc y s he (by omega) hy0 hy1 hz hpre
  · exact genAlloc impl hap R hmk' b L zp zl zc xp xl xc y s he (by omega) hy0 hy1 (by omega) hpre

/-- **`nat.divW`** (amd64): `z.divW(x, y)` (`y ≠ 0`, `x` normalised) returns a normalised nat holding `X / y`, in
`z`'s array (`zc ≥ len x`) or a fresh one, and `X % y`; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (Pre R b L zp zc xp xl y) (Post R b L zp zc xp xl y) := by
  rw [show names = LibDivW.names from rfl, ← LibDivW.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk hmv b L zp zl zc xp xl xc y) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      hpre⟩ fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv b L zp zl zc xp xl xc y) (A64.noExit_restrict64 hap names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.DivW
