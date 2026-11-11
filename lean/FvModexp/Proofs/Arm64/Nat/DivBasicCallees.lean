import FvModexp.Proofs.Arm64.Nat.DivBasicDefs
import FvModexp.Proofs.Arm64.Nat.AsmCallees

/-!
# `divBasic` (arm64): the callees, moved into `LibDivBasic.program`

`divWW`, `reciprocalWord` (asm's library summaries; `codeIn_lib`), `mulAddVWW.abi0` / `subVV.abi0` / `addVV.abi0`
with the runtime invariant carried over (`Callees.Summary0.live`), the deferred closure `nat.divBasic.deferwrap1`
(`Restore`'s proof re-run on this program), `(*stack).nat` (premise, `toSummaryRegs2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

theorem fetchIn_cons_cases {A : Segment} {rest : List Segment} {pc w : Nat}
    (h : Program.fetchIn (A :: rest) pc = some w) :
    Program.fetchIn [A] pc = some w ∨ Program.fetchIn rest pc = some w := by
  rw [Program.fetchIn_cons] at h
  rw [Program.fetchIn_cons]
  split at h
  · rename_i hc
    rw [if_pos hc]
    split at h
    · left; exact h
    · right; exact h
  · right; exact h

theorem fetchIn_some_mem : ∀ {segs : List Segment} {pc w : Nat}, Program.fetchIn segs pc = some w →
    ∃ seg ∈ segs, Program.fetchIn [seg] pc = some w
  | [], _, _, h => by simp [Program.fetchIn] at h
  | A :: rest, _, _, h => by
    rcases fetchIn_cons_cases h with h1 | h1
    · exact ⟨A, List.mem_cons_self .., h1⟩
    · obtain ⟨seg, hm, hs⟩ := fetchIn_some_mem h1
      exact ⟨seg, List.mem_cons_of_mem _ hm, hs⟩

theorem codeIn_lib (impl : List Segment) (hap : ImplApart Extracted.program impl) {lp : Program}
    (hm : ∀ seg ∈ lp.segments, seg ∈ Extracted.program.segments ∧ names.contains seg.name = true) :
    CodeIn lp (LibDivBasic.program.link impl) := by
  rw [LibDivBasic.eq_only]
  intro pc w hf
  obtain ⟨seg, hseg, hf'⟩ := fetchIn_some_mem (segs := lp.segments) hf
  obtain ⟨hm1, hm2⟩ := hm seg hseg
  exact codeIn_single (lp := { lp with segments := [seg] }) hap rfl hm1 hm2 pc w hf'

set_option maxRecDepth 100000 in
theorem codeIn_divww (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.DivWWA64.program (LibDivBasic.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.DivWWA64.program.segments = [Extracted.seg63] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
  exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 63) (by decide), by decide⟩

set_option maxRecDepth 100000 in
theorem codeIn_recip (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.RecipA64.program (LibDivBasic.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.RecipA64.program.segments = [Extracted.seg61, Extracted.seg62] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 61) (by decide), by decide⟩
  · exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 62) (by decide), by decide⟩

set_option maxRecDepth 100000 in
theorem codeIn_vww (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.MulAddVWWA64.program (LibDivBasic.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.MulAddVWWA64.program.segments = [Extracted.seg64] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
  exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 64) (by decide), by decide⟩

/-- `divWW` (arm64, asm): `X0, X1 = (u1·B + u0) / d, mod d` for `u1 < d`, `X3 = recip d`. -/
theorem divww (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDivBasic.program.link impl) FvModexp.Lib.DivWWA64.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ (s.regs 2).toNat ≠ 0 ∧
        (s.regs 0).toNat < (s.regs 2).toNat ∧ (s.regs 3).toNat = FvModexp.AsmDiv.recipWord (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧
        s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat) ∧
        s'.regs 1 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat) ∧
        s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ MemFrame s.mem s'.mem []) := by
  refine Summary.mono (Summary.of_codeIn (codeIn_divww impl hap) FvModexp.Arm64.DivWWSum.divWW_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5 18 (by decide), h5 28 (by decide), h5 29 (by decide), h6⟩

/-- `reciprocalWord` (arm64, asm), `d ≠ 0`. -/
theorem recip (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDivBasic.program.link impl) FvModexp.Lib.RecipA64.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 48 ∧ StackOK s 88 0 ∧
        (s.regs 0).toNat ≠ 0 ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 88)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧
        s'.regs 0 = BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord (s.regs 0).toNat) ∧
        s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat - 40)]) := by
  refine Summary.mono (Summary.of_codeIn (codeIn_recip impl hap) FvModexp.Arm64.RecipWordSum.recip_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, h5, h6, _, _, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h9⟩

def vwwFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.mulAddVWW.abi0"

/-- `mulAddVWW.abi0` with the runtime invariant and the stack guard carried over (= `MulAddWW.VLPre`). -/
abbrev VLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  MulAddVWWSum.Pre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
    Outside (s.sp.toNat + 72) 8 R.rt ∧
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ((s.regs 28).toNat + 16) 8 ∧
    Apart (s.sp.toNat + 72) 8 ((s.regs 28).toNat + 16) 8

/-- = asm `MulAddVWWSum.Q` (`lv` = `natVal`), reducible so that `janus_run` destructures it. -/
abbrev VQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
      (natVal s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
          s.mem.readLE (s.sp.toNat + 56) 8 + s.mem.readLE (s.sp.toNat + 64) 8) %
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  m.readLE (s.sp.toNat + 72) 8 =
      (natVal s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
          s.mem.readLE (s.sp.toNat + 56) 8 + s.mem.readLE (s.sp.toNat + 64) 8) /
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 72, s.sp.toNat + 80)]

abbrev VLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  VQ s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem vww (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivBasic.program.link impl) (segAddr Extracted.program vwwFn) (VLPre R b L) (VLQ R b L) := by
  have he : segAddr Extracted.program vwwFn = FvModexp.Lib.MulAddVWWA64.entry := by decide
  rw [he]
  have h0 := EqHashModel.Summary.of_codeIn (codeIn_vww impl hap) MulAddVWWSum.mulAddVWW_summary
  refine Summary0.mono (Callees.Summary0.live h0 (fun s => [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 72, s.sp.toNat + 80)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2⟩
  refine ⟨hp, hi, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega

theorem subvv (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivBasic.program.link impl) (segAddr Extracted.program subVVfn) (VVLPre R b L) (SubVVLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [subVVfn]).link impl) (LibDivBasic.program.link impl) := by
    rw [LibDivBasic.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact SubVVHyp.live (Summary.of_codeIn c (subVVHyp impl hap)) R b L

theorem addvv (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDivBasic.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L) (VVLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [addVVfn]).link impl) (LibDivBasic.program.link impl) := by
    rw [LibDivBasic.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact AddVVHyp.live (Summary.of_codeIn c (addVVHyp impl hap)) R b L

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic.deferwrap1"

theorem dfnA_eq : segAddr LibDivBasic.program fnD = dfnA := by decide

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore(stk.save())` closure (`Restore.sum`'s proof on this program) -/
theorem dsum (impl : List Segment) :
    Summary (LibDivBasic.program.link impl) dfnA Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

end FvModexp.Arm64.DivBasic
