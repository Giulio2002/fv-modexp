import FvModexp.Proofs.Amd64.Nat.TruncMain
import FvModexp.Proofs.Amd64.Nat.TruncMainA
import FvModexp.Proofs.Amd64.Nat.TruncSet
import FvModexp.Proofs.Amd64.Nat.TruncSetA
import FvModexp.Proofs.Amd64.Nat.TruncZero

/-!
# `nat.trunc` (amd64): the summary

`full`: the `Summary` at the entry (paths: empty result with empty `z` (`zeroPath`), `set` path (`len x < w`: reuse /
allocate), main path (`w ≤ len x`: reuse / allocate)); `ens : Hyp2` = infra's amd64 `EvenHyp.TruncHyp` shape with the
amended precondition (posts carry `s'.fsBase = s.fsBase ∧ s'.df = s.df`, AMD64 DF CONVENTION).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Trunc

/-- the entry precondition of the internal summary -/
@[reducible] def EntryP (s : State) (zp zl zc x xl xc n : Nat) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
    s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧ s.regs 7 = BitVec.ofNat 64 x ∧
    s.regs 6 = BitVec.ofNat 64 xl ∧ s.regs 8 = BitVec.ofNat 64 xc ∧ s.regs 9 = BitVec.ofNat 64 n

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) :
    Summary (LibTrunc.program.link impl) (segAddr Extracted.program fn)
      (fun s => EntryP s zp zl zc x xl xc n ∧ Pre R b L zp zl zc x xl n s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc x xl n s s') := by
  intro s hpc ⟨⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩, hpre⟩
  have he : Entry s zp zl zc x xl xc n := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibTrunc.program.link impl) := by
    rw [LibTrunc.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibTrunc.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  have hal := hpre.2.2
  by_cases hz0 : zc = 0 ∧ EvenHyp.truncNeed xl n = 0
  · have hzx : zp = x := by
      rcases hal with h | h | h
      · exact h
      · omega
      · unfold EvenHyp.truncNeed at hz0; unfold wOf at *; omega
    exact zeroPath impl R b L zp zl zc x xl xc n s he hz0.1 hz0.2 hzx hpre
  by_cases hset : xl < wOf n
  · by_cases hz : xl ≤ zc
    · exact setReuse impl R hmv' b L zp zl zc x xl xc n s he hset hz
        (by unfold EvenHyp.truncNeed at hz0; unfold wOf at *; omega) hpre
    · exact setAlloc impl R hmk' hmv' b L zp zl zc x xl xc n s he hset (by omega) hpre
  · by_cases hz : wOf n ≤ zc
    · exact mainReuse impl R hmv' b L zp zl zc x xl xc n s he (by omega) hz
        (by unfold EvenHyp.truncNeed at hz0; unfold wOf at *; omega) hpre
    · exact mainAlloc impl R hmk' hmv' b L zp zl zc x xl xc n s he (by omega) (by omega) hpre

/-- **`nat.trunc`** (amd64): `z.trunc(x, n)` returns a normalised nat holding `X mod 2^n`, in `z`'s array (`cap z ≥
min(len x, ⌈n/64⌉)`) or a fresh one; writes only `z`'s array and the window; keeps `FS` and `DF`; no panic, no
fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    Hyp2 impl R names 4192 64 := by
  intro b L z zl zc x xl xc n
  rw [show names = LibTrunc.names from rfl, ← LibTrunc.eq_only]
  janus64_ensures_old [FvModexp.Amd64.EvenHyp.TruncPre, FvModexp.NatNorm, FvModexp.Amd64.CallEnv, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.win, FvModexp.Amd64.TlsOK, FvModexp.NatLive]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk hmv b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      n.toNat) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, by simp [h_a0], by simp [h_a1],
      by simp [h_a2], by simp [h_a3], by simp [h_a4], by simp [h_a5], by simp [h_a6]⟩, hpre⟩
    fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

end FvModexp.Amd64.Trunc
