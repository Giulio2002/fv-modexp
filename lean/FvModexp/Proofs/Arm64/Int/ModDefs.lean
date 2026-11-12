import FvModexp.Proofs.Arm64.Int.LibMod
import FvModexp.Proofs.Arm64.Exp.RdIn0
import FvModexp.Proofs.Arm64.Top.RunIface

/-!
# `(*Int).Mod` (arm64): the `nat.div` premise at `(*Int).QuoRem`'s call, and the local spec form (agent divmc)

`z.Mod(z, y)` (int.go:325) calls `q.QuoRem(x = z, y, r = z)` (int.go:331, `q` a zeroed `Int` on Mod's frame), which calls
`q.abs.div(nil, r.abs, x.abs, y.abs)` (int.go:300): **`stk == nil`** (natdiv.go:538 `getStack()` / deferred `stk.free()`)
and **`z2 = u`** (the remainder storage IS the dividend: same pointer, length, capacity), `z = q.abs = nil`.
`DivHypM` states `nat.div` for exactly these arguments (X0..X3 = 0, X4..X6 = X7..X9 = u, X10..X12 = v), in the shape of
`ExpHyp.DivHyp` (same conjuncts where they apply; the stack ones replaced by `RunIface.PoolG`, as for `nat.expNN`'s
`stk == nil` path). Only the remainder is stated (Mod ignores the quotient; its array is a fresh runtime object, inside
`R.rt`, so the frame below covers its writes).

`ModX`: the one fact `RunIface.ModSpec`'s precondition lacks (NOTES-conventions "[divmc s28]"): `z`'s array (written
in place by `div`, when reused) is apart from the threshold globals that `divLarge`/`divRecursiveStep`/`nat.mul` read
after writing it. `ModSpecX` = `ModSpec` with `ModX` as a last pre conjunct (switched to `ModSpec` once it has it).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IMod

open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut NatOF RtPost)
open FvModexp.Arm64.RunIface (Serves Globals PoolG IntPre IntPost IntV IntLenLe maxW ModBudget lenW)

/-- `nat.div`'s precondition at `QuoRem`'s call from `Mod` (`z = nil`, `stk = nil`, `z2 = u`) -/
@[reducible] def DivPreM (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (u ul uc v vl : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ Globals R s.mem (win s stk above) ∧ ul ≤ uc ∧
    WrOut R L s stk above u uc ∧ RdIn0 R L s stk above u ul ∧ RdIn R L s stk above v vl ∧
    ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧ NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    (0 < uc → Apart u (8 * uc) v (8 * vl) ∧ Apart u (8 * uc) RunIface.gA 32) ∧
    PoolG R s.mem (win s stk above) ∧
    cost ul vl ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- `nat.div`'s postcondition there: the remainder `(r, rl, rc)` (X3..X5) holds `u mod v`, normalised, in `u`'s array
or a fresh one; the quotient (X0..X2) is unconstrained; memory changes only in the runtime, the window and `u`'s array -/
@[reducible] def DivPostM (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (u ul uc v vl : Nat) (s s' : State) : Prop :=
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 1 = BitVec.ofNat 64 ql ∧
    s'.regs 2 = BitVec.ofNat 64 qc ∧ s'.regs 3 = BitVec.ofNat 64 r ∧ s'.regs 4 = BitVec.ofNat 64 rl ∧
    s'.regs 5 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem u uc 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b (cost ul vl) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(u, u + 8 * uc)]) ∧
      LiveFrame s.mem s'.mem L [(u, u + 8 * uc)]

/-- **`nat.div`** as `(*Int).QuoRem` calls it from `(*Int).Mod`: `nil.div(nil, u, u, v)` (owner: asm) -/
def DivHypM (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program ExpHyp.fnDiv)
      [0#64, 0#64, 0#64, 0#64, u, ul, uc, u, ul, uc, v, vl, vc]
      (fun s => DivPreM R b cost L stk above u.toNat ul.toNat uc.toNat v.toNat vl.toNat s)
      (fun s s' => DivPostM R b cost L stk above u.toNat ul.toNat uc.toNat v.toNat vl.toNat s s')

/-- the fact `ModSpec`'s precondition lacks: `z`'s array (when it has one) is apart from the threshold globals -/
def ModX (m : Memory) (z : Nat) : Prop :=
  0 < m.readLE (z + 24) 8 → Apart (m.readLE (z + 8) 8) (8 * m.readLE (z + 24) 8) RunIface.gA 32

/-- `RunIface.ModSpec` with `ModX` as the last precondition conjunct -/
def ModSpecX (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments RunIface.namesMod).link impl)
      (segAddr Extracted.program (RunIface.P ++ "(*Int).Mod")) [z, z, y]
      (fun s => IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above) ∧
        ModX s.mem z.toNat)
      (fun s s' => s'.regs 0 = z ∧ IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

theorem namesMod_eq : RunIface.namesMod = LibMod.names := rfl

end FvModexp.Arm64.IMod
