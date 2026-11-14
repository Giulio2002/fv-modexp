import FvModexp.Proofs.Amd64.Exp.P2PreWbC

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the joins after `powers[0]` (agent divmc s64; twin of infra's
`Arm64/Exp/P2PreJ` / `P2PreX0` / `P2PreWbC` (`KeepB`))

`HeadJ … i`: from the main loop head `+0x388` with `RAX = i` (even, `2 ≤ i ≤ len`), `RDX = powers`, the context,
`powers[j]` computed for `j < i` and untouched (`PwT`) for `i ≤ j < len`, the budget spent so far (`trunc(x)` and
`i/2 - 1` rounds), the function returns with the postcondition. `RS0 … k`: `powers[j]` computed for `j < k`, untouched
for `k < j`. `JT`: the join after `powers[1] = trunc(x, logM)` returns (`+0x31b`). `KeepB`: the reads of `buf` kept.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

/-- the main loop head -/
abbrev pcH : Nat := 0x5e8900 + 0x388

/-- the return address of the `trunc(x)` call -/
abbrev pcT : Nat := 0x5e8900 + 0x31b

/-- the value of `powers[j]` -/
abbrev PV (lm x xl : Nat) (s : State) (j : Nat) : Nat := Exp.p2Pow lm (natVal s.mem x xl) j

/-- **HeadJ i**: the main loop head -/
def HeadJ (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State) (i : Nat) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc b L st pw pl ws lm x xl s → S.rip = BitVec.ofNat 64 pcH → Frm s S 176 →
    S.regs 0 = BitVec.ofNat 64 i → S.regs 2 = BitVec.ofNat 64 pw →
    Ctx R kc L st pw pl lm x xl s bp S.mem L1 b1 →
    (∀ j, j < i → PwD S.mem pw bp lm (natVal s.mem x xl) j) → (∀ j, i ≤ j → j < pl → PwT S.mem pw bp lm j) →
    i % 2 = 0 → 2 ≤ i → i ≤ pl → b - (tC lm + (i / 2 - 1) * rc lm) ≤ b1 →
    Goal impl R kc b L st pw pl lm x xl s S

/-- the round facts without loop locals: `powers[j]` computed for `j < k`, untouched for `k < j` -/
structure RS0 (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) (X bp : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) (k : Nat) : Prop where
  c : Ctx R kc L st pw pl lm x xl s bp M L1 b1
  d : ∀ j, j < k → PwD M pw bp lm X j
  t : ∀ j, k < j → j < pl → PwT M pw bp lm j

/-- **JT**: the return of `powers[1].trunc(x, logM)` (`RAX, RBX, RCX` = the result `(bp + 8 w, l, 2 w)`) -/
def JT (impl : List Amd64.Segment) (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat))
    (st pw pl ws lm x xl : Nat) (s : State) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 l : Nat),
    Pre R kc b L st pw pl ws lm x xl s → S.rip = BitVec.ofNat 64 pcT → Frm s S 176 →
    S.regs 0 = BitVec.ofNat 64 (bp + 8 * (1 * W lm)) → S.regs 3 = BitVec.ofNat 64 l →
    S.regs 1 = BitVec.ofNat 64 (2 * W lm) →
    RS0 R kc L st pw pl lm x xl s (natVal s.mem x xl) bp S.mem L1 b1 1 → l ≤ W lm →
    natVal S.mem (bp + 8 * (1 * W lm)) l = PV lm x xl s 1 → NatNorm S.mem (bp + 8 * (1 * W lm)) l →
    b - tC lm ≤ b1 →
    Goal impl R kc b L st pw pl lm x xl s S

/-- the reads of `buf` are kept -/
@[reducible] def KeepB (bp nb : Nat) (M M' : Memory) : Prop :=
  ∀ a n, 0 < n → bp ≤ a → a + n ≤ bp + 8 * nb → M'.readLE a n = M.readLE a n

theorem keepB_trans {bp nb : Nat} {M M' M'' : Memory} (h1 : KeepB bp nb M M') (h2 : KeepB bp nb M' M'') :
    KeepB bp nb M M'' := fun a n h0 ha hb => (h2 a n h0 ha hb).trans (h1 a n h0 ha hb)

/-- a nat inside `buf`: value and normalisation transfer -/
theorem nat_keepB {bp nb : Nat} {M M' : Memory} (h : KeepB bp nb M M') {p l : Nat} (h1 : bp ≤ p)
    (h2 : p + 8 * l ≤ bp + 8 * nb) : natVal M' p l = natVal M p l ∧ (NatNorm M p l → NatNorm M' p l) := by
  refine ⟨?_, fun hn => ?_⟩
  · rcases Nat.eq_zero_or_pos l with rfl | h0
    · simp [natVal, Janus.Arm64.Memory.readLE]
    · exact h p (8 * l) (by omega) h1 h2
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    rcases hn with hn | hn
    · exact Or.inl hn
    · refine Or.inr ?_
      rw [h _ 8 (by omega) (by omega) (by omega)]
      exact hn

/-- `powers[j]`'s words lie in `buf` -/
theorem pw_in {pl lm j bp : Nat} (hj : j + 2 ≤ pl + 1) :
    bp + 8 * (j * W lm) + 8 * (2 * W lm) ≤ bp + 8 * NB pl lm := by
  have : (j + 2) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ hj
  simp only [NB]; rw [Nat.add_mul] at this; omega

/-- two `powers` slots `j < k` do not overlap -/
theorem pw_sep {lm j k : Nat} (h : j < k) : j * W lm + W lm ≤ k * W lm := by
  have : (j + 1) * W lm ≤ k * W lm := Nat.mul_le_mul_right _ h
  rw [Nat.add_mul, Nat.one_mul] at this; exact this

section
variable {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State}

theorem rs0_next {X bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (h : RS0 R kc L st pw pl lm x xl s X bp M L1 b1 k) (hd : PwD M pw bp lm X k) :
    RS0 R kc L st pw pl lm x xl s X bp M L1 b1 (k + 1) :=
  ⟨h.c, fun j hj => by
    rcases Nat.lt_or_ge j k with h1 | h1
    · exact h.d j h1
    · rw [show j = k by omega]; exact hd, fun j hj hjp => h.t j (by omega) hjp⟩

end

end FvModexp.Amd64.P2Pre
