import FvModexp.Proofs.Arm64.Nat.DivMBase
import FvModexp.Proofs.Arm64.Int.ModDefs

set_option autoImplicit false

/-!
# `nat.div` (arm64) as `(*Int).QuoRem` calls it from `(*Int).Mod`: `nil.div(nil, u, u, v)` — definitions

divmc's `IMod.DivHypM` (Arm64/Int/ModDefs.lean, NOTES-conventions "[divmc s28] REQUEST asm"): `z = nil` (X0..X2 = 0),
`stk = nil` (X3 = 0: `getStack()` = `sync.(*Pool).Get(&stackPool)` or `newobject(type:big.stack)`, deferred
`stk.free()` = `nat.div.deferwrap1`), `z2 = u` (X4..X6 = X7..X9: the remainder overwrites the dividend in place).
Window `41504`, `above = 112` (as the stack-given form); budget `costM dc ul vl` = the stack-given budget at an empty new
stack plus the 24-byte `newobject`. `PFM`: `IMod.DivPreM`'s conjuncts by name.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatDiv
@[reducible] def PreM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s : State) : Prop :=
  IMod.DivPreM R b (costM dc) L 41504 112 u ul uc v vl s

@[reducible] def PostM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s s' : State) : Prop :=
  IMod.DivPostM R b (costM dc) L 41504 112 u ul uc v vl s s'

/-- the return relation: callee-saved registers and `PostM` -/
@[reducible] def RQM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    PostM R b dc L u ul uc v vl s s'

theorem PreM.f {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)} {u ul uc v vl : Nat}
    {s : State} (h : PreM R b dc L u ul uc v vl s) : PFM R b dc L u ul uc v vl s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

end FvModexp.Arm64.NatDiv
