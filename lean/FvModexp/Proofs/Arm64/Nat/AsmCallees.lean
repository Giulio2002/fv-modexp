import FvModexp.Proofs.Arm64.Nat.Callees
import FvModexp.Proofs.Arm64.AddVVSum
import FvModexp.Proofs.Arm64.AddMulVVWWSum

/-!
# The asm premises of the mul/div summaries, discharged by agent asm's library summaries (arm64)

`AddVVHyp impl` and `AddMulVVWWHyp impl` (`Callees`) from `AddVVSum.addVV_summary` / `AddMulVVWWSum.addMulVVWW_summary`
(proved on the one-segment library programs `Lib.AddVVA64` / `Lib.AddMulVVWWA64`, whose segment is literally the Run
extraction's `Extracted.seg28` / `Extracted.seg65`): `codeIn_single` moves them into the restricted programs.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Callees

theorem addVVHyp (impl : List Segment) (hap : ImplApart Extracted.program impl) : AddVVHyp impl := by
  have hseg : FvModexp.Lib.AddVVA64.segments = [Extracted.program.segments[28]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.AddVVA64.program) (ns := [addVVfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 28) (by decide)) (by decide)
  have he : segAddr Extracted.program addVVfn = FvModexp.Lib.AddVVA64.entry := by decide
  unfold AddVVHyp; rw [he]
  refine Janus.Contracts.EqHashModel.Summary.of_codeIn hc
    (Summary0.mono FvModexp.Arm64.AddVVSum.addVV_summary ?_ (fun _ _ _ hq => hq))
  intro s ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩

theorem addMulVVWWHyp (impl : List Segment) (hap : ImplApart Extracted.program impl) : AddMulVVWWHyp impl := by
  have hseg : FvModexp.Lib.AddMulVVWWA64.segments = [Extracted.program.segments[65]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.AddMulVVWWA64.program) (ns := [addMulVVWWfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 65) (by decide)) (by decide)
  have he : segAddr Extracted.program addMulVVWWfn = FvModexp.Lib.AddMulVVWWA64.entry := by decide
  unfold AddMulVVWWHyp; rw [he]
  refine Janus.Contracts.EqHashModel.Summary.of_codeIn hc
    (Summary0.mono FvModexp.Arm64.AddMulVVWWSum.addMulVVWW_summary ?_ (fun _ _ _ hq => hq))
  intro s ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

end FvModexp.Arm64.Callees
