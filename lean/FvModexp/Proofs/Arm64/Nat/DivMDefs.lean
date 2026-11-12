import FvModexp.Proofs.Arm64.Nat.DivRel
import FvModexp.Proofs.Arm64.Nat.DivW0
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

/-- the budget of the `stk == nil` form -/
@[reducible] def costM (dc : Nat → Nat → Nat → Nat) (ul vl : Nat) : Nat := cost dc 0 ul vl + 24

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

/-- `IMod.DivPreM`'s conjuncts by name -/
structure PFM (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vl : Nat) (s : State) : Prop where
  ce : CallEnv R L s 41504 112
  sv : RunIface.Serves R
  gl : RunIface.Globals R s.mem (win s 41504 112)
  ulc : ul ≤ uc
  uo : ExpHyp.WrOut R L s 41504 112 u uc
  ui : ExpHyp.RdIn0 R L s 41504 112 u ul
  vo : ExpHyp.RdIn R L s 41504 112 v vl
  ul9 : ul ≤ 2 ^ 9
  v0 : 0 < vl
  vl9 : vl ≤ 2 ^ 9
  un : NatNorm s.mem u ul
  vn : NatNorm s.mem v vl
  ug : 0 < uc → Apart u (8 * uc) v (8 * vl) ∧ Apart u (8 * uc) RunIface.gA 32
  pg : RunIface.PoolG R s.mem (win s 41504 112)
  cost : costM dc ul vl ≤ b
  inv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

theorem PreM.f {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)} {u ul uc v vl : Nat}
    {s : State} (h : PreM R b dc L u ul uc v vl s) : PFM R b dc L u ul uc v vl s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- `ul > 0` ⇒ `uc > 0` and `u` is a readable input -/
theorem PFM.uin {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)} {u ul uc v vl : Nat}
    {s : State} (hp : PFM R b dc L u ul uc v vl s) (hu : 0 < ul) : ExpHyp.RdIn R L s 41504 112 u ul :=
  hp.ui.2 hu

set_option linter.defProp false in
/-- `nat.divW` (`DivW.ens0`, possibly-nil empty dividend) as a summary in `LibDiv.program.link impl` -/
def wsum0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :=
  Ensures.toSummaryIn (DivW.ens0 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) (noExit_restrict hap DivW.names)
    (show CodeIn ((Extracted.program.onlySegments DivW.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide)))

end FvModexp.Arm64.NatDiv
