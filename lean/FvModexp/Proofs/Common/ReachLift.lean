import Janus

/-!
# Moving a `Reaches` to a bigger program (arm64)

A run of `p` that ends in an outcome is a run of any `P` with `p`'s code at the same addresses, the same stubs and the
same exit address (`run_mono`): every fetched word of `p` is `P`'s, and `p`'s run never fetches outside its code
(that is a fault, not an outcome). `Reaches.mono` is the `Reaches` form. Used to put a sub-path proved on a callee
program (`LibN`) into the program of the recursive pair (`LibNE`).
-/

set_option autoImplicit false

namespace FvModexp

open Janus Janus.Arm64 Janus.Tactic

theorem run_mono {p P : Program} (hf : ∀ pc w, p.fetch pc = some w → P.fetch pc = some w)
    (hs : P.stubs = p.stubs) (he : P.exitAddr = p.exitAddr) :
    ∀ (n : Nat) (s : State) (o : Outcome), p.run n s = .ok o → P.run n s = .ok o := by
  intro n
  induction n with
  | zero => intro s o h; simp [Program.run] at h
  | succ n ih =>
    intro s o h
    have hst : P.stubAt s.pc.toNat = p.stubAt s.pc.toNat := by simp only [Program.stubAt, hs]
    simp only [Program.run] at h ⊢
    rw [he, hst]
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [if_pos hx] at h ⊢; exact h
    · rw [if_neg hx] at h ⊢
      cases hsb : p.stubAt s.pc.toNat with
      | some st => rw [hsb] at h; exact h
      | none =>
        rw [hsb] at h
        cases hfe : p.fetch s.pc.toNat with
        | none => rw [hfe] at h; cases h
        | some w =>
          rw [hfe] at h
          rw [hf _ _ hfe]
          dsimp only at h ⊢
          revert h
          cases Arm64.step w s with
          | error e => intro h; cases h
          | ok s' => intro h; exact ih s' o h

theorem Reaches.mono {p P : Program} (hf : ∀ pc w, p.fetch pc = some w → P.fetch pc = some w)
    (hs : P.stubs = p.stubs) (he : P.exitAddr = p.exitAddr) {s : State} {Q : Outcome → Prop}
    (h : Reaches p s Q) : Reaches P s Q := by
  obtain ⟨n, o, hr, hq⟩ := h
  exact ⟨n, o, run_mono hf hs he n s o hr, hq⟩

end FvModexp
