import FvModexp.Proofs.Arm64.Nat.DivW

/-!
# `nat.divW` (arm64) without the `memmove(z, x, 0)` side condition

`DivW.Pre`'s last conjunct (`len x = 0 → y = 1 → zp = xp ∨ z's empty range held`) is only there for `z.set(x)` with
`len x = 0`, where Go's `copy` calls `memmove(zp, xp, 0)` and Janus v0.2.0's `MemmoveLive` asks for the (empty)
destination to be held. With the zero-length contract `MemmoveZeroLive` (Janus PR #2, local copy
`Janus.Contracts.MemmoveZeroLive`) as an extra premise the conjunct is dropped: `Pre2` = `Pre` without it, `ens2`/`sum2`.
`nat.div` (whose `z` may be an arbitrary `nil` slice) uses this form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivW

set_option maxRecDepth 20000 in
theorem full2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDivW.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = y ∧
        Pre2 R b L zp zc xp xl y s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  by_cases hz : xl.toNat = 0 ∧ y.toNat = 1
  · have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibDivW.program.link impl) := by
      rw [LibDivW.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibDivW.names
    have hx : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hz.1)
    have hy : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hz.2)
    subst hx hy
    exact setZero impl R (MemmoveZeroLive.of_codeIn hc3 hmz) b L zp zl zc xp xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6
      hpre
  · exact full impl hap R hmk hmv hmz b L zp zl zc xp xl xc y s hpc
      ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre.toPre fun a b => absurd ⟨a, b⟩ hz⟩

/-- **`nat.divW`** (arm64), `Pre2` form (premise: the zero-length `memmove` contract) -/
theorem ens2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (Pre2 R b L zp zc xp xl y) (Post R b L zp zc xp xl y) := by
  janus_ensures_old [FvModexp.Arm64.DivW.Pre2, FvModexp.Arm64.CallEnv, FvModexp.Arm64.DivW.wordT, FvModexp.NatLive, FvModexp.Arm64.win, FvModexp.NatNorm, Janus.Spec.GuardOK, Janus.Spec.StackOK]
  rw [show names = LibDivW.names from rfl, ← LibDivW.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full2 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.DivW
