import FvModexp.Proofs.Amd64.Conv

set_option autoImplicit false

/-!
# Reads that are empty or apart from the return slot survive `setRet` (amd64)

Since Janus v0.4.0 the precondition of `Ensures` is evaluated BEFORE the return address is written at `[RSP, RSP + 8)` (`State.setRet`), and the
proof needs `pre s → pre (s.setRet ret)` (`janus64_pre_setRet`). The tactic rewrites a read `readLE a n` of the state when `[a, a + n)` is
apart from the slot, the side goal `a + n ≤ RSP ∨ RSP + 8 ≤ a` being discharged by `omega` from the precondition. A read of a possibly EMPTY
object (`natVal m p n` / `NatNorm m p n` / `bytesAt m p n` with a length `n` that may be `0`, whose location facts are stated under `0 < n` only)
has no such side goal in the empty case, although a read of 0 bytes is `0` whatever the memory holds. These conditional rewrites carry the
empty case as a disjunct, so the tactic discharges them from the same facts (the lemmas are passed to `janus64_pre_setRet [..]`; the
definition `NatNorm` is then NOT unfolded, since its read sits under the `n ≠ 0` guard that the side goal needs).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Spec Janus.Contracts

namespace FvModexp.Amd64

/-- A read of `n` bytes is unchanged by installing the return address when it is empty or apart from `[RSP, RSP + 8)`. -/
theorem readLE_setRet_or_zero {s : State} {ret a n : Nat}
    (h : n = 0 ∨ a + n ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ a) :
    (s.setRet ret).mem.readLE a n = s.mem.readLE a n := by
  rcases h with h | h
  · subst h; rfl
  · exact readLE_setRet_of_disjoint h

/-- `NatNorm` of the `n` limbs at `p` is unchanged by installing the return address when the nat is empty or its limbs are apart from the
return slot. -/
theorem natNorm_setRet {s : State} {ret p n : Nat}
    (h : n = 0 ∨ p + 8 * n ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ p) :
    FvModexp.NatNorm (s.setRet ret).mem p n = FvModexp.NatNorm s.mem p n := by
  unfold FvModexp.NatNorm
  by_cases hn : n = 0
  · simp [hn]
  · have h2 : (s.setRet ret).mem.readLE (p + 8 * (n - 1)) 8 = s.mem.readLE (p + 8 * (n - 1)) 8 :=
      readLE_setRet_of_disjoint (by omega)
    rw [h2]

/-- `∀ p n, (p, n) ∈ [(a, c), (b, d)] → P p n` (the shape of `NHyp.RemPreQ`'s operand facts `∀ p n, (p, n) ∈ [(up, ul), (vp, vl)] → …`) as a
conjunction: with the pair quantifier expanded, the apartness of each operand from the return slot is visible to `janus64_pre_setRet`. -/
theorem forall_mem_pair2 {α β : Type} (P : α → β → Prop) (a b : α) (c d : β) :
    (∀ (p : α) (n : β), (p, n) ∈ [(a, c), (b, d)] → P p n) ↔ P a c ∧ P b d := by
  constructor
  · intro h; exact ⟨h a c (by simp), h b d (by simp)⟩
  · rintro ⟨h1, h2⟩ p n hm
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption

/-- The return slot `[RSP, RSP + 8)` lies in the call window, so it is outside the runtime-owned ranges (`CallEnv`, `8 ≤ above`). -/
theorem CallEnv.slot {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above : Nat} (h : CallEnv R L s stk above)
    (hab : 8 ≤ above) : Outside (s.regs 4).toNat 8 R.rt :=
  Janus.Outside.of_sub h.2.2.2.2.1 (by have := h.2.1.1; simp only [regSP] at this; omega) (by omega)


/-- The three-operand twin of `forall_mem_pair2` (`NHyp.SlowHyp`'s operand list `[(x, xl), (y, yl), (m, ml)]`). -/
theorem forall_mem_pair3 {α β : Type} (P : α → β → Prop) (a b c : α) (d e f : β) :
    (∀ (p : α) (n : β), (p, n) ∈ [(a, d), (b, e), (c, f)] → P p n) ↔ P a d ∧ P b e ∧ P c f := by
  constructor
  · intro h; exact ⟨h a d (by simp), h b e (by simp), h c f (by simp)⟩
  · rintro ⟨h1, h2, h3⟩ p n hm
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption

end FvModexp.Amd64
