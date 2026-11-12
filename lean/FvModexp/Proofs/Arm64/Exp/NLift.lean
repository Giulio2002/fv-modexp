import FvModexp.Proofs.Arm64.Exp.LibN
import FvModexp.Proofs.Arm64.Exp.LibNE
import FvModexp.Proofs.Common.Link
import FvModexp.Proofs.Common.ReachLift

/-!
# `nat.expNN` (arm64): from `LibN` (expNN's callee program) to `LibNE` (the recursive pair expNN ↔ expNNEven)

`liftNE`: a sub-path of expNN proved on `LibN.program.link impl` is a sub-path on `LibNE.program.link impl`
(`LibN.names ⊆ LibNE.names`, same stubs and exit).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.EqHashModel FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- the position in `LibNE.names` of each name of `LibN.names` (generated; checked by `n_idx`) -/
def nIdx : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77]

/-- one string equality per name (instead of the quadratic `contains` sweep) -/
theorem n_idx : LibN.names.map some = nIdx.map (fun i => LibNE.names[i]?) := by decide +kernel

theorem names_sub : ∀ x, LibN.names.contains x = true → LibNE.names.contains x = true := by
  intro x hx
  have h1 : some x ∈ LibN.names.map some := List.mem_map_of_mem (List.elem_iff.1 hx)
  rw [n_idx] at h1
  obtain ⟨i, -, hi⟩ := List.mem_map.1 h1
  exact List.elem_iff.2 (List.mem_of_getElem? hi)

theorem codeInNE (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (LibN.program.link impl) (LibNE.program.link impl) := by
  have hc := codeIn_restrict_mono hap names_sub
  rwa [← LibN.eq_only, ← LibNE.eq_only] at hc

theorem liftNE (impl : List Segment) (hap : ImplApart Extracted.program impl) {r : Nat} {S : State}
    {Q : Outcome → Prop} (h : Reaches ((LibN.program.link impl).withExit r) S Q) :
    Reaches ((LibNE.program.link impl).withExit r) S Q := by
  have hc := codeInNE impl hap
  refine Reaches.mono (p := (LibN.program.link impl).withExit r) (P := (LibNE.program.link impl).withExit r)
    (fun pc w hf => (hc pc w hf).1) ?_ rfl h
  simp only [Program.withExit, Program.link]
  rw [LibN.eq_only, LibNE.eq_only]; rfl

theorem segs_sub (impl : List Segment) {seg : Segment} (h : seg ∈ (LibN.program.link impl).segments) :
    seg ∈ (LibNE.program.link impl).segments := by
  rw [LibN.eq_only] at h; rw [LibNE.eq_only]
  simp only [Program.link, Program.onlySegments, List.mem_append, List.mem_filter] at h ⊢
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, names_sub _ h2⟩
  · exact Or.inr h

/-- a return address of `LibNE`'s code is one of `LibN`'s -/
theorem retAddr_down {impl : List Segment} {r : Nat} (h : RetAddr (LibNE.program.link impl) r) :
    RetAddr (LibN.program.link impl) r :=
  ⟨h.aligned, h.user, fun seg hs => h.notCode seg (segs_sub impl hs), fun st hs => h.notStub st (by
    rw [LibN.eq_only] at hs; rw [LibNE.eq_only]; exact hs)⟩

end FvModexp.Arm64.ExpN
