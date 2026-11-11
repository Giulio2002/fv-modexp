import FvModexp.Proofs.Arm64.Top.RunC2Sum

/-! # `Run` (arm64): the return sites of the `Mod` and `exp` calls are admissible return addresses of the callees'
programs

`janus_run … calls [expW …]` must prove the callee summary's `RetAddr ((Extracted.program.onlySegments namesExp).link impl)
(X30)` at the call; proved inside the caller's run, the kernel re-checks the segment filter by name (`names.contains`
over every segment) as part of the caller's proof term, which made `RunC2EX`'s exp-call declaration ~3.6 GB of kernel
memory (and a `decide` of the same fact alone 7.1 GB). Here it is proved from the layout: `Run` is the extraction's
first segment, no kept callee is named `Run`, and the segments are pairwise apart (`ImplApart`). The facts enter the
callers as hypotheses (`janus_run` uses a `RetAddr` hypothesis from the context). Return sites: `fn + 0x87c` (after
`CALL (*Int).exp`, `0x20393c`) and `fn + 0x85c` (after `CALL (*Int).Mod`, `0x20391c`). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- A return site inside `Run`'s segment (the extraction's first) is admissible for a callee program that does not keep
`Run`. -/
theorem raRun (impl : List Segment) (hap : ImplApart Extracted.program impl) (names : List String)
    (hfn : names.contains fn = false) (ret : Nat) (hal : ret % 4 = 0)
    (hin : ∀ seg0 rest, Extracted.program.segments = seg0 :: rest →
      seg0.name = fn ∧ seg0.base ≤ ret ∧ ret < seg0.base + 4 * seg0.words.length ∧ ret < 2 ^ 48)
    (hst : ∀ st ∈ Extracted.program.stubs, st.addr ≠ ret) :
    RetAddr ((Extracted.program.onlySegments names).link impl) ret := by
  obtain ⟨seg0, rest, hs⟩ : ∃ a l, Extracted.program.segments = a :: l := ⟨_, _, rfl⟩
  obtain ⟨hnm, h1, h2, hu⟩ := hin seg0 rest hs
  have hpw := hap.1
  rw [hs, List.cons_append, List.pairwise_cons] at hpw
  refine RetAddr.of_placement hal hu ⟨seg0, by rw [hs]; exact List.mem_cons_self .., h1, h2⟩ hap.1 ?_ hst
  intro seg hm hn
  rw [hs] at hm
  rcases List.mem_cons.1 hm with rfl | hm
  · rw [hnm, hfn] at hn; exact absurd hn (by decide)
  · have ha := hpw.1 seg (List.mem_append_left _ hm)
    unfold Segment.Apart at ha
    omega

set_option maxRecDepth 20000 in
theorem raExp (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments RunIface.namesExp).link impl) 2111804 :=
  raRun impl hap _ (by decide) _ (by decide) (fun _ _ h => by cases h; decide) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem raMod (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments RunIface.namesMod).link impl) 2111772 :=
  raRun impl hap _ (by decide) _ (by decide) (fun _ _ h => by cases h; decide) (by decide +kernel)

end FvModexp.Arm64.Run
