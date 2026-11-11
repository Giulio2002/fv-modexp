import FvModexp.Proofs.Arm64.Top.RunDefs

/-! # `Run` (arm64): return sites of `Run`'s calls are admissible return addresses of the callees' programs

A callee summary built by `Ensures.toSummaryIn` has the precondition `RetAddr ((Extracted.program.onlySegments names).link
impl) (X30)`. Proved by `janus_run` inside the caller's run, the kernel re-checks the segment filter by name
(`names.contains` over every one of the 84 segments) as part of the caller's proof term (≈ 3.6 GB of kernel memory for
the `exp` call; a `decide` of the fact alone 7.1 GB). `raRun` proves it from the layout instead: `Run` is the
extraction's first segment, the callee program does not keep `Run`, and the segments are pairwise apart (`ImplApart`).
The callers put `raXxx impl hap` into the context before the run (`janus_run` uses a `RetAddr` hypothesis from the
context). Return sites (`0x…` = link addresses, `fn = 0x2030c0`): `math/big.nat.setBytes` calls at `0x203190`,
`0x203248`, `0x203308` (headers), the fix's `nat.setBytes` at `0x2035e4`, `0x20370c`, `0x203810` (operands). -/

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
/-- The return sites of the three header `setBytes` calls (`math/big`). -/
theorem raSBS (impl : List Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (h : ret = 0x203194 ∨ ret = 0x20324c ∨ ret = 0x20330c) :
    RetAddr ((Extracted.program.onlySegments [SetBytesStd.fn]).link impl) ret := by
  rcases h with rfl | rfl | rfl <;>
    exact raRun impl hap _ (by decide) _ (by decide) (fun _ _ h => by cases h; decide) (by decide +kernel)

set_option maxRecDepth 20000 in
/-- The return sites of the three operand `setBytes` calls (`go-bigmodexpfix`). -/
theorem raSB (impl : List Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (h : ret = 0x2035e8 ∨ ret = 0x203710 ∨ ret = 0x203814) :
    RetAddr ((Extracted.program.onlySegments [SetBytes.fn]).link impl) ret := by
  rcases h with rfl | rfl | rfl <;>
    exact raRun impl hap _ (by decide) _ (by decide) (fun _ _ h => by cases h; decide) (by decide +kernel)

end FvModexp.Arm64.Run
