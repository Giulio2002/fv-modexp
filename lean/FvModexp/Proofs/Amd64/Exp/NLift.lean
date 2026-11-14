import FvModexp.Proofs.Amd64.Exp.LibN
import FvModexp.Proofs.Amd64.Exp.LibNE
import FvModexp.Proofs.Common.Link

/-!
# `nat.expNN` (amd64): from `LibN` (expNN's callee program) to `LibNE` (the recursive pair expNN ↔ expNNEven)
(agent expmc s73; twin of Arm64/Exp/NLift.lean, with the amd64 `run_mono64` of Common/ReachLift.lean)

`liftNE`: a sub-path of expNN proved on `LibN.program.link impl` is a sub-path on `LibNE.program.link impl`
(`LibN.names ⊆ LibNE.names`, same stubs and exit). `retAddr_down`: a return address of `LibNE` is one of `LibN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.EqHashModel FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpN

theorem run_mono64 {p P : Amd64.Program} (hf : ∀ pc w, p.fetch pc = some w → P.fetch pc = some w)
    (hs : P.stubs = p.stubs) (he : P.exitAddr = p.exitAddr) :
    ∀ (n : Nat) (s : State) (o : Amd64.Outcome), p.run n s = .ok o → P.run n s = .ok o := by
  intro n
  induction n with
  | zero => intro s o h; simp [Amd64.Program.run] at h
  | succ n ih =>
    intro s o h
    have hst : P.stubAt s.rip.toNat = p.stubAt s.rip.toNat := by simp only [Amd64.Program.stubAt, hs]
    simp only [Amd64.Program.run] at h ⊢
    rw [he, hst]
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [if_pos hx] at h ⊢; exact h
    · rw [if_neg hx] at h ⊢
      cases hsb : p.stubAt s.rip.toNat with
      | some st => rw [hsb] at h; exact h
      | none =>
        rw [hsb] at h
        cases hfe : p.fetch s.rip.toNat with
        | none => rw [hfe] at h; cases h
        | some w =>
          rw [hfe] at h
          rw [hf _ _ hfe]
          dsimp only at h ⊢
          revert h
          cases Amd64.step w s with
          | error e => intro h; cases h
          | ok s' => intro h; exact ih s' o h

theorem reaches_mono64 {p P : Amd64.Program} (hf : ∀ pc w, p.fetch pc = some w → P.fetch pc = some w)
    (hs : P.stubs = p.stubs) (he : P.exitAddr = p.exitAddr) {s : State} {Q : Amd64.Outcome → Prop}
    (h : Reaches p s Q) : Reaches P s Q := by
  obtain ⟨n, o, hr, hq⟩ := h
  exact ⟨n, o, run_mono64 hf hs he n s o hr, hq⟩

/-- the position in `LibNE.names` of each name of `LibN.names` (generated; checked by `n_idx`) -/
def nIdx : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75]

/-- one string equality per name (instead of the quadratic `contains` sweep) -/
theorem n_idx : LibN.names.map some = nIdx.map (fun i => LibNE.names[i]?) := by decide +kernel

theorem names_sub : ∀ x, LibN.names.contains x = true → LibNE.names.contains x = true := by
  intro x hx
  have h1 : some x ∈ LibN.names.map some := List.mem_map_of_mem (List.elem_iff.1 hx)
  rw [n_idx] at h1
  obtain ⟨i, -, hi⟩ := List.mem_map.1 h1
  exact List.elem_iff.2 (List.mem_of_getElem? hi)

theorem codeInNE (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 (LibN.program.link impl) (LibNE.program.link impl) := by
  have hc := A64.codeIn_restrict_mono64 hap names_sub
  rwa [← LibN.eq_only, ← LibNE.eq_only] at hc

theorem liftNE (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {r : Nat} {S : State}
    {Q : Amd64.Outcome → Prop} (h : Reaches ((LibN.program.link impl).withExit r) S Q) :
    Reaches ((LibNE.program.link impl).withExit r) S Q := by
  have hc := codeInNE impl hap
  refine reaches_mono64 (p := (LibN.program.link impl).withExit r) (P := (LibNE.program.link impl).withExit r)
    (fun pc w hf => (hc pc w hf).1) ?_ rfl h
  simp only [Amd64.Program.withExit, Amd64.Program.link]
  rw [LibN.eq_only, LibNE.eq_only]; rfl

theorem segs_sub (impl : List Amd64.Segment) {seg : Amd64.Segment} (h : seg ∈ (LibN.program.link impl).segments) :
    seg ∈ (LibNE.program.link impl).segments := by
  rw [LibN.eq_only] at h; rw [LibNE.eq_only]
  simp only [Amd64.Program.link, Amd64.Program.onlySegments, List.mem_append, List.mem_filter] at h ⊢
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, names_sub _ h2⟩
  · exact Or.inr h

/-- a return address of `LibNE`'s code is one of `LibN`'s -/
theorem retAddr_down {impl : List Amd64.Segment} {r : Nat} (h : RetAddr (LibNE.program.link impl) r) :
    RetAddr (LibN.program.link impl) r :=
  ⟨h.user, fun seg hs => h.notCode seg (segs_sub impl hs), fun st hs => h.notStub st (by
    rw [LibN.eq_only] at hs; rw [LibNE.eq_only]; exact hs)⟩

end FvModexp.Amd64.ExpN
