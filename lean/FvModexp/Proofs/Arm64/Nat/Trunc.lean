import FvModexp.Proofs.Arm64.Nat.TruncSet
import FvModexp.Proofs.Arm64.Nat.TruncZero

/-!
# `nat.trunc` (arm64): the summary

`full`: the `Summary` at the entry (paths: empty result with empty `z` (`zeroPath`), `set` path (`len x < w`: reuse /
allocate), main path (`w ≤ len x`: reuse / allocate)); `ens`; `hyp` = infra's `TruncHyp` shape with the amended
precondition (`Hyp2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Trunc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) :
    Summary (LibTrunc.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
        s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧ s.regs 3 = BitVec.ofNat 64 x ∧
        s.regs 4 = BitVec.ofNat 64 xl ∧ s.regs 5 = BitVec.ofNat 64 xc ∧ s.regs 6 = BitVec.ofNat 64 n ∧
        Pre R b L zp zl zc x xl n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibTrunc.program.link impl) := by
    rw [LibTrunc.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibTrunc.names
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  have hal := hpre.2.2
  by_cases hz0 : zc = 0 ∧ EvenHyp.truncNeed xl n = 0
  · have hzx : zp = x := by
      rcases hal with h | h | h
      · exact h
      · omega
      · unfold EvenHyp.truncNeed at hz0; unfold wOf at *; omega
    exact zeroPath impl R b L zp zl zc x xl xc n s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hz0.1 hz0.2 hzx hpre
  by_cases hset : xl < wOf n
  · by_cases hz : xl ≤ zc
    · exact setReuse impl R hmv' b L zp zl zc x xl xc n s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hset hz
        (by unfold EvenHyp.truncNeed at hz0; unfold wOf at *; omega) hpre
    · exact setAlloc impl R hmk' hmv' b L zp zl zc x xl xc n s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hset (by omega) hpre
  · by_cases hz : wOf n ≤ zc
    · exact mainReuse impl R hmv' b L zp zl zc x xl xc n s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega) hz
        (by unfold EvenHyp.truncNeed at hz0; unfold wOf at *; omega) hpre
    · exact mainAlloc impl R hmk' hmv' b L zp zl zc x xl xc n s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (by omega)
        (by omega) hpre

/-- **`nat.trunc`** (arm64): `z.trunc(x, n)` returns a normalised nat holding `X mod 2^n`, in `z`'s array (`cap z ≥
min(len x, ⌈n/64⌉)`) or a fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : Hyp2 impl R names 4208 64 := by
  intro b L z zl zc x xl xc n
  rw [show names = LibTrunc.names from rfl, ← LibTrunc.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk hmv b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat n.toNat)
    hret h_pc h_lr ⟨?_, ?_, by simp [h_x0], by simp [h_x1], by simp [h_x2], by simp [h_x3], by simp [h_x4],
      by simp [h_x5], by simp [h_x6], hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.Trunc
