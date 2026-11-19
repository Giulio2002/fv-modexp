import FvModexp.Proofs.Amd64.Top.RunDefs

/-! # `Run` (amd64): return sites of `Run`'s calls are admissible return addresses of the callees' programs

The amd64 twin of the arm64 `RunRA` (docs/history/PERF-log.md "top s9": proving the callee summary's `RetAddr` inside `janus64_run`
makes the kernel re-check the segment filter by name). `raRun` proves it from the layout: `Run` is the extraction's first
segment (`seg0`, base `0x654340`), the callee program does not keep it, segments are pairwise apart (`ImplApart`).
`retAddr_restrict` is adapted from agent infra's `Amd64/Exp/CallW.lean`. Return sites: std `nat.setBytes` (headers)
`0x654450`, `0x65455c`, `0x65467a`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hR _ _ (hp.1 a ha')
      · exact pairwise_ne hR hp.2 ha' hb' hne

theorem find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact find_none_of h x hx'

theorem retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
    {ns : List String} {cs : Amd64.Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat)
    (hi : i < cs.bytes.length) (hu : cs.base + i < 2 ^ 47) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + i) := by
  refine ⟨hu, fun seg hseg => ?_, fun st hst => ?_⟩
  · have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have hne : seg ≠ cs := by
      rintro rfl
      rcases List.mem_append.1 hseg with h | h
      · have := (List.mem_filter.1 h).2
        rw [hn] at this; exact absurd this (by decide)
      · have := hap.1
        rw [List.pairwise_append] at this
        have := this.2.2 seg hcs seg h
        unfold Amd64.Segment.Apart at this
        omega
    have := pairwise_ne (fun a b h => by unfold Amd64.Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Amd64.Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Amd64.Program.stubAt at h1
    have := find_none_of h1 st hst
    simp at this
    exact this

/-- A return site inside `Run`'s segment (`seg0`) is admissible for a callee program that does not keep `Run`. -/
theorem raRun (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (names : List String)
    (hfn : names.contains Extracted.seg0.name = false) (i : Nat) (hi : i < Extracted.seg0.bytes.length) (hu : i < 0x10000) :
    RetAddr ((Extracted.program.onlySegments names).link impl) (0x654340 + i) := by
  have hb : Extracted.seg0.base = 0x654340 := rfl
  rw [← hb]
  exact retAddr_restrict hap (cs := Extracted.seg0) (by show Extracted.seg0 ∈ Extracted.seg0 :: _; exact List.mem_cons_self ..)
    hfn i hi (by rw [hb]; omega)

set_option maxRecDepth 20000 in
/-- The return sites of the three header `setBytes` calls (`math/big`). -/
theorem raSBS (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (h : ret = 0x654450 ∨ ret = 0x65455c ∨ ret = 0x65467a) :
    RetAddr ((Extracted.program.onlySegments [SetBytesStd.fn]).link impl) ret := by
  rcases h with rfl | rfl | rfl
  · exact raRun impl hap _ (by decide) 0x110 (by decide +kernel) (by decide)
  · exact raRun impl hap _ (by decide) 0x21c (by decide +kernel) (by decide)
  · exact raRun impl hap _ (by decide) 0x33a (by decide +kernel) (by decide)

end FvModexp.Amd64.Run
