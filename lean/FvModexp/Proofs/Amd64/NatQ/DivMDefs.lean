import FvModexp.Proofs.Amd64.NatQ.DivMBase
import FvModexp.Proofs.Amd64.Int.ModDivHyp

set_option autoImplicit false

/-!
# `nat.div` (amd64) as `(*Int).QuoRem` calls it from `(*Int).Mod`: `nil.div(nil, u, u, v)` — definitions (top s39)

Twin of Arm64/NatQ/DivMDefs.lean on top's amd64 `IMod.DivHypM` (Amd64/Int/ModDivHyp.lean): `z = nil` (RAX, RBX, RCX = 0),
`stk = nil` (RDI = 0: `getStack()` = `sync.(*Pool).Get(&stackPool)` or `newobject(type:big.stack)`, deferred
`stk.free()` = `nat.div.deferwrap1`), `z2 = u` (RSI, R8, R9 = the stack words `u, ul, uc`). Window `41512`, `above = 112`
(as the stack-given form); budget `costMQ dc ul vl`. `PFM`: `IMod.DivPreM`'s conjuncts by name.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatDiv

@[reducible] def PreM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl vc : Nat) (s : State) : Prop :=
  IMod.DivPreM R b (costMQ dc) L 41512 112 u ul uc v vl vc s

@[reducible] def PostM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s s' : State) : Prop :=
  IMod.DivPostM R b (costMQ dc) L 41512 112 u ul uc v vl s s'

/-- the return relation: callee-saved registers and `PostM` -/
@[reducible] def RQM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s s' : State) : Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    PostM R b dc L u ul uc v vl s s'

theorem PreM.f {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat}
    {s : State} (h : PreM R b dc L u ul uc v vl vc s) : PFM R b dc L u ul uc v vl vc s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

end FvModexp.Amd64.Q.NatDiv
