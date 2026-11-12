import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# Widening the program of an `Ensures` (arm64, agent infra)

`ens_widen`: an `Ensures` about `(P.onlySegments ns).link impl` is one about `(P.onlySegments ms).link impl` for every
`ms ⊇ ns` (a return address outside the bigger program's code is outside the smaller one's; the run is the same code).
Used to put callee summaries proved on their own function sets (`StackNat.names`, `Lsh.names`, …) under the one name
list a composition (`ExpEven.full`, `ModInv.ens`) takes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace FvModexp.Arm64.EnsWiden

theorem argsFrom_of {s : State} : ∀ (args : List W64) (k : Nat),
    (∀ i (hi : i < args.length), s.regs (k + i) = args[i]) → ArgsFrom s k args
  | [], _, _ => trivial
  | a :: l, k, h => ⟨by have := h 0 (by simp); simpa using this, argsFrom_of l (k + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this⟩

theorem retAddr_narrow {P : Program} {impl : List Segment} {ns ms : List String}
    (hsub : ∀ x, ns.contains x = true → ms.contains x = true) {ret : Nat}
    (h : RetAddr ((P.onlySegments ms).link impl) ret) : RetAddr ((P.onlySegments ns).link impl) ret := by
  refine ⟨h.aligned, h.user, fun seg hseg => h.notCode seg ?_, fun st hst => h.notStub st hst⟩
  rcases List.mem_append.1 hseg with h1 | h1
  · obtain ⟨hm, hc⟩ := List.mem_filter.1 h1
    exact List.mem_append_left _ (List.mem_filter.2 ⟨hm, hsub _ hc⟩)
  · exact List.mem_append_right _ h1

/-- **Widening**: `Ensures` on the functions `ns` gives `Ensures` on any `ms ⊇ ns`. -/
theorem ens_widen {P : Program} {impl : List Segment} (hap : ImplApart P impl) {ns ms : List String}
    (hsub : ∀ x, ns.contains x = true → ms.contains x = true) {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((P.onlySegments ns).link impl) entry args pre post) :
    Ensures ((P.onlySegments ms).link impl) entry args pre post := by
  intro ret hret s hcs hpre
  have hsum := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hsub)
  have hlr : s.regs 30 = BitVec.ofNat 64 ret := by
    have := hcs.lr; simp only [Program.exitAddr_withExit] at this; exact this
  have hlrN : (s.regs 30).toNat = ret := by
    rw [hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
  refine Summary.returns hsum hret hcs.pc hlr ⟨?_, argsFrom_of args 0 fun i hi => by simpa using hcs.args i hi, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  rw [show regLR = 30 from rfl, hlrN]; exact retAddr_narrow hsub hret

end FvModexp.Arm64.EnsWiden
