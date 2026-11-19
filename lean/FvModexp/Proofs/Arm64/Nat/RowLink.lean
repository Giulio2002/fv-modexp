import FvModexp.Proofs.Arm64.Conv

/-!
# From a summary on the restricted program to a standalone row (arm64)

A row's main theorem must be about `Extracted.program.link impl` (Janus audit, round 14). `Ensures.full` moves an `ens`
proved on `(Extracted.program.onlySegments ns).link impl` (CONVENTIONS §3) to it: the restricted program's code is the
full program's code (`codeIn_restrict_of_apart`), and a return address admissible for the full program is admissible for
the restricted one.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64

theorem retAddr_restrict {P : Program} {impl : List Segment} {ns : List String} {ret : Nat}
    (h : RetAddr (P.link impl) ret) : RetAddr ((P.onlySegments ns).link impl) ret :=
  ⟨h.aligned, h.user, fun seg hseg => h.notCode seg (by
    rcases List.mem_append.1 hseg with hs | hs
    · exact List.mem_append_left _ (List.mem_filter.1 hs).1
    · exact List.mem_append_right _ hs), h.notStub⟩

theorem argsFrom_of {s : State} : ∀ {args : List W64} {k : Nat}, (∀ i (h : i < args.length), s.regs (k + i) = args[i]) →
    ArgsFrom s k args
  | [], _, _ => trivial
  | a :: l, k, h => ⟨h 0 (Nat.zero_lt_succ _), argsFrom_of fun i hi => by
      have := h (i + 1) (by simpa using hi); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this⟩

theorem Ensures.full {P : Program} {impl : List Segment} (hap : ImplApart P impl) {ns : List String} {entry : Nat}
    {args : List W64} {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((P.onlySegments ns).link impl) entry args pre post) (hinv : Ensures.SetRetInv (P.link impl) entry args pre := by janus_pre_setRet) [ArgsFit args] : Ensures (P.link impl) entry args pre post := by
  refine Ensures.of_old hinv ?_
  intro ret hret s hs hpre
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_of_apart hap ns)
  have hlr : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
  refine Summary.returns hS hret hs.pc hlr ⟨?_, argsFrom_of (fun i hi => by simpa using hs.args i hi), hpre⟩ ?_
  · rw [hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
    exact retAddr_restrict hret
  · intro s' ⟨⟨h1, h2, h3, h4⟩, hp⟩
    exact ⟨⟨h1, h2, h3, h4⟩, hp⟩

end FvModexp.Arm64
