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

theorem names_all : LibN.names.all (fun x => LibNE.names.contains x) = true := by decide +kernel

theorem names_sub : ∀ x, LibN.names.contains x = true → LibNE.names.contains x = true := by
  intro x hx
  have h := List.all_eq_true.1 names_all x (List.elem_iff.1 hx)
  exact h

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
