import Janus

set_option autoImplicit false

/-!
# Dropping `X30` conjuncts from a row precondition (agent infra s49)

The final-gate RA rule (BRIEF "RETURN-ADDRESS PIN GAP") forbids row preconditions that constrain the return address
(`X30`) beyond the framework ABI. Internal summaries that need `X30 % 4 = 0 ∧ X30 < 2^48` (the final `RET`) get them
from the ABI: `CallSetup.lr` (`X30 = ret`) and `RetAddr.aligned` / `RetAddr.user`.
-/

open Janus Janus.Arm64 Janus.GoABI

namespace FvModexp.Arm64.RAx30

/-- the `X30` facts from the ABI -/
theorem x30_of {p : Program} {e : Nat} {args : List (BitVec 64)} {s : State} {ret : Nat}
    (hret : RetAddr p ret) (hs : CallSetup (p.withExit ret) e args s) :
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 := by
  have h : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
  have hu := hret.user
  have e : (BitVec.ofNat 64 ret).toNat = ret := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [h, e]
  exact ⟨hret.aligned, hu⟩

/-- an `Ensures` whose precondition follows from `pre'` plus the ABI's `X30` facts holds on `pre'` -/
theorem ens_drop {p : Program} {e : Nat} {args : List (BitVec 64)} {pre pre' : State → Prop}
    {post : State → State → Prop}
    (hpre : ∀ s, pre' s → (s.regs 30).toNat % 4 = 0 → (s.regs 30).toNat < 2 ^ 48 → pre s)
    (h : Ensures p e args pre post) : Ensures p e args pre' post := by
  intro ret hret s hs hp
  obtain ⟨h1, h2⟩ := x30_of hret hs
  exact h ret hret s hs (hpre s hp h1 h2)

end FvModexp.Arm64.RAx30
