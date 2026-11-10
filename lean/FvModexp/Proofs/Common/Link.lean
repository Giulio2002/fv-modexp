import Janus

/-!
# Restricted programs: moving a callee's theorem into its caller's program (both ISAs)

See `docs/CONVENTIONS.md` §3. Every function proof of the project is an `Ensures` about
`(Extracted.program.onlySegments names).link impl`: the function's own code and the code of every
extracted function it (transitively) calls, `names`, plus the runtime stand-in `impl`. A caller with
`names' ⊇ names` uses it through `Ensures.toSummaryIn` with

* `codeIn_restrict_mono` (`…64`): the callee's program is code of the caller's program;
* `noExit_restrict` (`…64`): the restricted program has no code at the exit address.

Both follow from the one premise on `impl` the auditor allows, `ImplApart Extracted.program impl`.
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Contracts.EqHashModel

/-- Filtering by `ns` after filtering by `ms ⊇ ns` is filtering by `ns`. -/
theorem filter_filter_sub {α : Type} (f g : α → Bool) (h : ∀ x, f x = true → g x = true) (l : List α) :
    (l.filter g).filter f = l.filter f := by
  rw [List.filter_filter]
  congr 1
  funext x
  cases hf : f x <;> simp [hf, h x]

/-- **arm64.** The program of a callee (names `ns`) is code of the program of a caller (names `ms ⊇ ns`). -/
theorem codeIn_restrict_mono {P : Program} {impl : List Segment} (hap : ImplApart P impl)
    {ns ms : List String} (hsub : ∀ x, ns.contains x = true → ms.contains x = true) :
    CodeIn ((P.onlySegments ns).link impl) ((P.onlySegments ms).link impl) := by
  have heq : P.onlySegments ns = (P.onlySegments ms).onlySegments ns := by
    simp only [Program.onlySegments]
    rw [filter_filter_sub (fun (seg : Janus.Segment) => ns.contains seg.name)
      (fun (seg : Janus.Segment) => ms.contains seg.name) (fun x hx => hsub _ hx)]
  rw [heq]
  refine codeIn_restrict (P.onlySegments ms) ns impl ?_ ?_
  · exact hap.1.sublist ((List.filter_sublist).append_right impl)
  · intro seg hseg i hi
    have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    exact hap.2 seg hseg' i hi

/-- **arm64.** A restricted program has no code at the exit address. -/
theorem noExit_restrict {P : Program} {impl : List Segment} (hap : ImplApart P impl) (ns : List String) :
    ((P.onlySegments ns).link impl).fetch ((P.onlySegments ns).link impl).exitAddr = none := by
  cases hf : ((P.onlySegments ns).link impl).fetch ((P.onlySegments ns).link impl).exitAddr with
  | none => rfl
  | some w =>
    exfalso
    have hf' : Program.fetchIn (P.segments.filter (fun seg => ns.contains seg.name) ++ impl) P.exitAddr = some w := hf
    obtain ⟨seg, hmem, i, hi, hpc⟩ := Program.fetchIn_index hf'
    have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hmem with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    exact (hap.2 seg hseg' i hi).2 hpc.symm

/-- **arm64.** The whole linked program contains the restricted one (the final theorem's program). -/
theorem codeIn_restrict_full {P : Program} {impl : List Segment} (hap : ImplApart P impl) (ns : List String) :
    CodeIn ((P.onlySegments ns).link impl) (P.link impl) := codeIn_restrict_of_apart hap ns

end FvModexp

namespace FvModexp.A64

open Janus.Contracts.EqHashModel
open Janus.Amd64 (Program Segment ImplApart codeIn_restrict64)

/-- **amd64.** The program of a callee (names `ns`) is code of the program of a caller (names `ms ⊇ ns`). -/
theorem codeIn_restrict_mono64 {P : Program} {impl : List Segment} (hap : ImplApart P impl)
    {ns ms : List String} (hsub : ∀ x, ns.contains x = true → ms.contains x = true) :
    CodeIn64 ((P.onlySegments ns).link impl) ((P.onlySegments ms).link impl) := by
  have heq : P.onlySegments ns = (P.onlySegments ms).onlySegments ns := by
    simp only [Program.onlySegments]
    rw [FvModexp.filter_filter_sub (fun (seg : Janus.Amd64.Segment) => ns.contains seg.name)
      (fun (seg : Janus.Amd64.Segment) => ms.contains seg.name) (fun x hx => hsub _ hx)]
  rw [heq]
  refine codeIn_restrict64 (P.onlySegments ms) ns impl ?_ ?_
  · exact hap.1.sublist ((List.filter_sublist).append_right impl)
  · intro seg hseg i hi
    have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    exact hap.2 seg hseg' i hi

/-- **amd64.** A restricted program has no code at the exit address. -/
theorem noExit_restrict64 {P : Program} {impl : List Segment} (hap : ImplApart P impl) (ns : List String) :
    ((P.onlySegments ns).link impl).fetch ((P.onlySegments ns).link impl).exitAddr = none := by
  cases hf : ((P.onlySegments ns).link impl).fetch ((P.onlySegments ns).link impl).exitAddr with
  | none => rfl
  | some w =>
    exfalso
    have hf' : Program.fetchIn (P.segments.filter (fun seg => ns.contains seg.name) ++ impl) P.exitAddr = some w := hf
    obtain ⟨seg, hmem, h1, h2⟩ := Program.fetchIn_index hf'
    have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hmem with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have := (hap.2 seg hseg' (P.exitAddr - seg.base) (by omega)).2
    exact this (by omega)

end FvModexp.A64

/-! ## Read-only data after a call

A summary's postcondition gives `MemFrame m m' (R.rt ++ ws)`, which says nothing about the region list; the run gives
`m'.regions = m.regions` (`Summary.regions`, `janus.callRegions`). With the data outside `R.rt` and the written ranges
`ws` writable, the data bytes are unchanged, so `DataLoaded` holds again (NOTES-divmc issue 1). -/

namespace FvModexp

open Janus Janus.Arm64

theorem dataLoaded_frame {p : Janus.Program} {m m' : Memory} {rt ws : List (Nat × Nat)} (hd : p.DataLoaded m)
    (hreg : m'.regions = m.regions) (hro : ∀ d ∈ p.data, Outside d.base d.bytes.length rt)
    (hf : MemFrame m m' (rt ++ ws)) (hws : ∀ r ∈ ws, m.accessible r.1 (r.2 - r.1) true = true) :
    p.DataLoaded m' := by
  intro d hdm
  obtain ⟨hr, hb⟩ := hd d hdm
  refine ⟨by rw [hreg]; exact hr, fun i hi => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdm
  have hout : Outside (p.data[k].base + i) 1 (rt ++ ws) := by
    rw [Janus.outside_append]
    refine ⟨(hro _ hdm).of_sub (by omega) (by omega), ?_⟩
    have : ∀ ws' : List (Nat × Nat), (∀ r ∈ ws', m.accessible r.1 (r.2 - r.1) true = true) →
        Outside (p.data[k].base + i) 1 ws' := by
      intro ws' h
      induction ws' with
      | nil => trivial
      | cons r rs ih =>
        refine ⟨?_, ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')⟩
        have := Janus.Tactic.disjoint_of_dataLoaded hd k hk (h r (List.mem_cons_self ..))
        omega
    exact this ws hws
  have := hf.readLE _ 1 hout
  simp only [Memory.readLE_one] at this
  rw [BitVec.eq_of_toNat_eq this]
  exact hb i hi

/-- amd64 twin. -/
theorem dataLoaded_frame64 {p : Janus.Amd64.Program} {m m' : Memory} {rt ws : List (Nat × Nat)} (hd : p.DataLoaded m)
    (hreg : m'.regions = m.regions) (hro : ∀ d ∈ p.data, Outside d.base d.bytes.length rt)
    (hf : MemFrame m m' (rt ++ ws)) (hws : ∀ r ∈ ws, m.accessible r.1 (r.2 - r.1) true = true) :
    p.DataLoaded m' := by
  intro d hdm
  obtain ⟨hr, hb⟩ := hd d hdm
  refine ⟨by rw [hreg]; exact hr, fun i hi => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdm
  have hout : Outside (p.data[k].base + i) 1 (rt ++ ws) := by
    rw [Janus.outside_append]
    refine ⟨(hro _ hdm).of_sub (by omega) (by omega), ?_⟩
    have : ∀ ws' : List (Nat × Nat), (∀ r ∈ ws', m.accessible r.1 (r.2 - r.1) true = true) →
        Outside (p.data[k].base + i) 1 ws' := by
      intro ws' h
      induction ws' with
      | nil => trivial
      | cons r rs ih =>
        refine ⟨?_, ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')⟩
        have := Janus.Amd64.Tactic.disjoint_of_dataLoaded hd k hk (h r (List.mem_cons_self ..))
        omega
    exact this ws hws
  have := hf.readLE _ 1 hout
  simp only [Memory.readLE_one] at this
  rw [BitVec.eq_of_toNat_eq this]
  exact hb i hi

end FvModexp
