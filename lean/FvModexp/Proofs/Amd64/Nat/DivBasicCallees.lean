import FvModexp.Proofs.Amd64.Nat.DivBasicDefs
import FvModexp.Proofs.Amd64.Nat.AsmCallees
import FvModexp.Proofs.Amd64.Nat.MulAddWWDefs
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `divBasic` (amd64): the callees, moved into `LibDivBasic.program`

`divWW` (asm's library summary), `mulAddVWW.abi0` / `subVV.abi0` / `addVV.abi0` with the runtime invariant carried
over (`Callees.Summary0.live`), the deferred closure `nat.divBasic.deferwrap1` (`Restore`'s proof re-run on this
program). `reciprocalWord` is inlined on amd64. The twin of `Arm64/Nat/DivBasicCallees.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 100000 in
theorem codeIn_divww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.DivWWAmd64.program (LibDivBasic.program.link impl) := by
  rw [LibDivBasic.eq_only]
  exact codeIn_single hap (seg := Extracted.seg61) rfl
    (List.getElem_mem (l := Extracted.program.segments) (n := 61) (by decide)) (by decide)

set_option maxRecDepth 100000 in
theorem codeIn_vww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.MulAddVWWAmd64.program (LibDivBasic.program.link impl) := by
  rw [LibDivBasic.eq_only]
  exact codeIn_single hap (seg := Extracted.seg62) rfl
    (List.getElem_mem (l := Extracted.program.segments) (n := 62) (by decide)) (by decide)

/-- `divWW` (amd64, asm): `RAX, RBX = (u1·B + u0) / d, mod d` for `u1 < d`, `RDI = recip d`. -/
theorem divww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibDivBasic.program.link impl) FvModexp.Lib.DivWWAmd64.entry
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 1).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 1).toNat ∧
        (s.regs 7).toNat = FvModexp.AsmDiv.recipWord (s.regs 1).toNat)
      (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8#64 ∧
        s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) / (s.regs 1).toNat) ∧
        s'.regs 3 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) % (s.regs 1).toNat) ∧
        s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧
        s'.regs 15 = s.regs 15 ∧ MemFrame s.mem s'.mem [] ∧
        s'.xmm = s.xmm ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df) := by
  refine Summary.mono (Summary.of_codeIn64 (codeIn_divww impl hap) FvModexp.Amd64.DivWWSum.divWW_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨h1, h2, h3, h4, h5 5 (by decide), h5 14 (by decide), h5 12 (by decide), h5 13 (by decide),
    h5 15 (by decide), h6, h7, h8, h9⟩

def vwwFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.mulAddVWW.abi0"

theorem vww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivBasic.program.link impl) (segAddr Extracted.program vwwFn) (MulAddWW.VLPre R b L)
      (MulAddWW.VLQ R b L) := by
  have he : segAddr Extracted.program vwwFn = FvModexp.Lib.MulAddVWWAmd64.entry := by decide
  rw [he]
  have h0 := Summary.of_codeIn64 (codeIn_vww impl hap) MulAddVWWSum.mulAddVWW_summary
  refine Summary0.mono (Callees.Summary0.live h0 (fun s => [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 72, (s.regs 4).toNat + 80)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2, ha3, ha4⟩
  refine ⟨hp, hi, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega
  · simp only [Outside, and_true]; unfold Apart at ha3 ha4; omega

theorem subvv (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivBasic.program.link impl) (segAddr Extracted.program subVVfn) (VVLPre R b L) (SubVVLQ R b L) := by
  have c : CodeIn64 ((Extracted.program.onlySegments [subVVfn]).link impl) (LibDivBasic.program.link impl) := by
    rw [LibDivBasic.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  exact SubVVHyp.live (Summary.of_codeIn64 c (subVVHyp impl hap)) R b L

theorem addvv (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivBasic.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L) (VVLQ R b L) := by
  have c : CodeIn64 ((Extracted.program.onlySegments [addVVfn]).link impl) (LibDivBasic.program.link impl) := by
    rw [LibDivBasic.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  exact AddVVHyp.live (Summary.of_codeIn64 c (addVVHyp impl hap)) R b L

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic.deferwrap1"

theorem dfnA_eq : segAddr LibDivBasic.program fnD = dfnA := by decide

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure (`BasicSqrDfr.dsum`'s proof on this program) -/
theorem dsum (impl : List Amd64.Segment) :
    Summary (LibDivBasic.program.link impl) dfnA Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

end FvModexp.Amd64.DivBasic
