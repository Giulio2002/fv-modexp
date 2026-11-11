import FvModexp.Proofs.Amd64.Nat.Callees
import FvModexp.Proofs.Amd64.AddVVSum
import FvModexp.Proofs.Amd64.AddMulVVWWSum
import FvModexp.Proofs.Amd64.SubVVSum

/-!
# The asm premises of the mul/div summaries, discharged by agent asm's library summaries (amd64)

As the arm64 twin: `AddVVSum.addVV_summary` / `AddMulVVWWSum.addMulVVWW_summary` moved by `codeIn_single` (the library
segment is literally the Run extraction's `Extracted.seg28` / `Extracted.seg63`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Callees

theorem addVVHyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) : AddVVHyp impl := by
  have hseg : FvModexp.Lib.AddVVAmd64.segments = [Extracted.program.segments[28]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.AddVVAmd64.program) (ns := [addVVfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 28) (by decide)) (by decide)
  have he : segAddr Extracted.program addVVfn = FvModexp.Lib.AddVVAmd64.entry := by decide
  unfold AddVVHyp; rw [he]
  refine Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc
    (Summary0.mono FvModexp.Amd64.AddVVSum.addVV_summary ?_ (fun _ _ _ hq => hq))
  intro s ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

theorem addMulVVWWHyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    AddMulVVWWHyp impl := by
  have hseg : FvModexp.Lib.AddMulVVWWAmd64.segments = [Extracted.program.segments[63]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.AddMulVVWWAmd64.program) (ns := [addMulVVWWfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 63) (by decide)) (by decide)
  have he : segAddr Extracted.program addMulVVWWfn = FvModexp.Lib.AddMulVVWWAmd64.entry := by decide
  unfold AddMulVVWWHyp; rw [he]
  refine Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc
    (Summary0.mono FvModexp.Amd64.AddMulVVWWSum.addMulVVWW_summary ?_ (fun _ _ _ hq => hq))
  intro s ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩


theorem subVVHyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) : SubVVHyp impl := by
  have hseg : FvModexp.Lib.SubVVAmd64.segments = [Extracted.program.segments[24]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.SubVVAmd64.program) (ns := [subVVfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 24) (by decide)) (by decide)
  have he : segAddr Extracted.program subVVfn = FvModexp.Lib.SubVVAmd64.entry := by decide
  unfold SubVVHyp; rw [he]
  refine Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc
    (Summary0.mono FvModexp.Amd64.SubVVSum.subVV_summary ?_ (fun _ _ _ hq => hq))
  intro s ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

end FvModexp.Amd64.Callees
