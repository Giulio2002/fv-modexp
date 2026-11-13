import FvModexp.Proofs.Arm64.Nat.StackNatXDefs

set_option autoImplicit false

/-!
# The Q-form runtime post (arm64; divmc, TIGHT COSTS — NOTES-conventions "[divmc s34] TIGHT COSTS step 2")

A Q-form summary with level-free consumption `C` at reserve level `H` (Common/StackPot) passes the interface cost
argument `c = C + stkR H s.mem st` (pre `c ≤ b`, as before) and states `RtPostQ R b c (stkR H s'.mem st) …`:
`b - c + r' ≤ b'` instead of `ExpHyp.RtPost`'s `b - c ≤ b'` (the credit `r'` of the grown capacity comes back).
-/

open Janus Janus.Arm64 Janus.Contracts

namespace FvModexp.Arm64

@[reducible] def RtPostQ (R : RtInv) (b cost r' : Nat) (L L' : List (Nat × Nat)) (b' : Nat) (s s' : State) : Prop :=
  LiveExt R L L' ∧ b - cost + r' ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)

/-- two sequential Q-form steps compose (`C1 + C2`), the memory between them keeping the stack capacity -/
theorem q_seq2 {H b b1 b2 C1 C2 : Nat} {m0 m1 m1' m2 : Memory} {st : Nat}
    (h1 : b - (C1 + stkR H m0 st) + stkR H m1 st ≤ b1) (hc : stCap m1' st = stCap m1 st)
    (h2 : b1 - (C2 + stkR H m1' st) + stkR H m2 st ≤ b2) (hpre : C1 + C2 + stkR H m0 st ≤ b) :
    C2 + stkR H m1' st ≤ b1 ∧ b - (C1 + C2 + stkR H m0 st) + stkR H m2 st ≤ b2 := by
  rw [stkR_congr hc] at h2 ⊢; omega

/-- a non-stack call (`b - c ≤ b'`, the capacity unchanged) inside a Q-form computation -/
theorem q_plainStep {H b b1 C1 : Nat} {m0 m1 : Memory} {st : Nat} (h1 : b - C1 ≤ b1) (hc : stCap m1 st = stCap m0 st)
    (hpre : C1 + stkR H m0 st ≤ b) : b - (C1 + stkR H m0 st) + stkR H m1 st ≤ b1 := by
  rw [stkR_congr hc]; omega

end FvModexp.Arm64
