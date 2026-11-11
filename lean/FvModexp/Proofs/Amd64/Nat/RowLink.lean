import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Common.Link

/-!
# From a summary on the restricted program to a standalone row (amd64; twin of `FvModexp.Arm64` RowLink)

A row's main theorem must be about `Extracted.program.link impl`. `Ensures.full64` moves an `ens` proved on
`(Extracted.program.onlySegments ns).link impl` (CONVENTIONS §3) to it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64

theorem retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} {ns : List String} {ret : Nat}
    (h : RetAddr (P.link impl) ret) : RetAddr ((P.onlySegments ns).link impl) ret :=
  ⟨h.user, fun seg hseg => h.notCode seg (by
    rcases List.mem_append.1 hseg with hs | hs
    · exact List.mem_append_left _ (List.mem_filter.1 hs).1
    · exact List.mem_append_right _ hs), h.notStub⟩

theorem argsFrom_of {s : State} : ∀ {args : List W64} {k : Nat},
    (∀ i (h : i < args.length), s.regs (argReg (k + i)) = args[i]) → ArgsFrom64 s k args
  | [], _, _ => trivial
  | a :: l, k, h => ⟨by simpa using h 0 (Nat.zero_lt_succ _), argsFrom_of fun i hi => by
      have := h (i + 1) (by simpa using hi); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this⟩

theorem Ensures.full64 {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl) {ns : List String} {entry : Nat}
    {args : List W64} {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((P.onlySegments ns).link impl) entry args pre post) : Ensures (P.link impl) entry args pre post := by
  intro ret hret s hs hpre
  have hS := Ensures.toSummaryIn h (FvModexp.A64.noExit_restrict64 hap ns) hlen (codeIn_restrict_of_apart64 hap ns)
  refine Summary.returns hS hret hs.rip (by rw [retAddrOf_eq, hs.ret]; rfl) ⟨?_, hs.zero,
    argsFrom_of (fun i hi => by simpa using hs.args i hi), hs.df, hpre⟩ ?_
  · rw [hs.ret]; exact retAddr_restrict hret
  · intro s' ⟨⟨h1, h2, h3, h4⟩, hp⟩
    exact ⟨⟨h1, h2, h3, h4⟩, hp⟩

end FvModexp.Amd64
