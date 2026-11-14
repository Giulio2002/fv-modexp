import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# Widening the program of an `Ensures` (amd64, agent divmc s75; port of Arm64/Exp/EnsWiden.lean by infra)

`ens_widen`: an `Ensures` about `(P.onlySegments ns).link impl` is one about `(P.onlySegments ms).link impl` for every
`ms ⊇ ns` (a return address outside the bigger program's code is outside the smaller one's; the run is the same code).
Used to put callee summaries proved on their own function sets (`Q.NatSqr.names`, `Q.NatMul.names`, …) under the one
name list a composition takes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace FvModexp.Amd64.EnsWiden

theorem argsFrom_of {s : State} : ∀ (args : List W64) (k : Nat),
    (∀ i (hi : i < args.length), s.regs (argReg (k + i)) = args[i]) → ArgsFrom64 s k args
  | [], _, _ => trivial
  | a :: l, k, h => ⟨by have := h 0 (by simp); simpa using this, argsFrom_of l (k + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this⟩

theorem retAddr_narrow {P : Amd64.Program} {impl : List Amd64.Segment} {ns ms : List String}
    (hsub : ∀ x, ns.contains x = true → ms.contains x = true) {ret : Nat}
    (h : RetAddr ((P.onlySegments ms).link impl) ret) : RetAddr ((P.onlySegments ns).link impl) ret := by
  refine ⟨h.user, fun seg hseg => h.notCode seg ?_, fun st hst => h.notStub st hst⟩
  rcases List.mem_append.1 hseg with h1 | h1
  · obtain ⟨hm, hc⟩ := List.mem_filter.1 h1
    exact List.mem_append_left _ (List.mem_filter.2 ⟨hm, hsub _ hc⟩)
  · exact List.mem_append_right _ h1

/-- **Widening** (amd64): `Ensures` on the functions `ns` gives `Ensures` on any `ms ⊇ ns`. -/
theorem ens_widen {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl) {ns ms : List String}
    (hsub : ∀ x, ns.contains x = true → ms.contains x = true) {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((P.onlySegments ns).link impl) entry args pre post) :
    Ensures ((P.onlySegments ms).link impl) entry args pre post := by
  intro ret hret s hcs hpre
  have hsum := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hcs.len (A64.codeIn_restrict_mono64 hap hsub)
  have hra : s.mem.readLE (s.regs regSP).toNat 8 = ret := by
    have := hcs.ret; simp only [Amd64.Program.exitAddr_withExit] at this; exact this
  refine Summary.returns hsum hret hcs.rip (by rw [retAddrOf, hra])
    ⟨?_, hcs.zero, argsFrom_of args 0 fun i hi => by simpa using hcs.args i hi, hcs.df, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  rw [hra]; exact retAddr_narrow hsub hret

end FvModexp.Amd64.EnsWiden
