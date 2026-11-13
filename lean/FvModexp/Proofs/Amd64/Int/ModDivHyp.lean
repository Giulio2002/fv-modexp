import FvModexp.Proofs.Amd64.Exp.ExpHyp
import FvModexp.Proofs.Amd64.Exp.RdIn0
import FvModexp.Proofs.Amd64.Top.RunIface

set_option autoImplicit false

/-!
# `(*Int).Mod` (amd64): the `nat.div` premise at `(*Int).QuoRem`'s call — `IMod.DivPreM` / `DivPostM` / `DivHypM` (top s39)

Text twin of divmc's Arm64/Int/ModDefs.lean `DivPreM` / `DivPostM` / `DivHypM` in the amd64 vocabulary (NOTES-conventions
"[top s39] amd64 stk == nil nat.div"). `z.Mod(z, y)` (int.go:325) calls `q.QuoRem(x = z, y, r = z)` (int.go:331), which
calls `q.abs.div(nil, r.abs, x.abs, y.abs)` (int.go:300): **`stk == nil`** (natdiv.go:538 `getStack()` / deferred
`stk.free()`) and **`z2 = u`** (the remainder storage IS the dividend), `z = q.abs = nil`.
amd64 ABIInternal (`ExpHyp.DivPre`'s layout): `z` RAX,RBX,RCX `= 0`, `stk` RDI `= 0`, `z2` RSI,R8,R9 `= u`; `u` and `v` on
the stack at `RSP + 8 … + 48` (named by the precondition, as `ExpHyp.DivPre`); results `q` RAX,RBX,RCX (`regs 0, 3, 1`),
`r` RDI,RSI,R8 (`regs 7, 6, 8`). Posts start with `s'.fsBase = s.fsBase ∧ s'.df = s.df` (DF CONVENTION); the TLS slot
`FS:-8` is apart from `u`'s array by `WrOut`. Only the remainder is stated (Mod ignores the quotient; its array is a
fresh runtime object, inside `R.rt`, so the frame below covers its writes). `ModX` is already part of the amd64
`RunIface.ModSpec`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.EvenHyp (RdIn RdIn0 WrOut RtPost)
open FvModexp.Amd64.ExpHyp (NatOF)
open FvModexp.Amd64.RunIface (Serves Globals PoolG)

/-- `nat.div`'s precondition at `QuoRem`'s call from `Mod` (`z = nil`, `stk = nil`, `z2 = u`; `u`, `v` on the stack) -/
@[reducible] def DivPreM (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (u ul uc v vl vc : Nat) (s : State) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = u ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc ∧ s.mem.readLE ((s.regs 4).toNat + 32) 8 = v ∧
    s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl ∧ s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc ∧
  CallEnv R L s stk above ∧ Serves R ∧ Globals R s.mem (win s stk above) ∧ ul ≤ uc ∧
    WrOut R L s stk above u uc ∧ RdIn0 R L s stk above u ul ∧ RdIn R L s stk above v vl ∧
    ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧ NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    (0 < uc → Apart u (8 * uc) v (8 * vl) ∧ Apart u (8 * uc) RunIface.gA 32) ∧
    PoolG R s.mem (win s stk above) ∧
    cost ul vl ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- `nat.div`'s postcondition there: the remainder `(r, rl, rc)` (RDI, RSI, R8) holds `u mod v`, normalised, in `u`'s
array or a fresh one; the quotient (RAX, RBX, RCX) is unconstrained; memory changes only in the runtime, the window and
`u`'s array -/
@[reducible] def DivPostM (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (u ul uc v vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem u uc 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b (cost ul vl) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(u, u + 8 * uc)]) ∧
      LiveFrame s.mem s'.mem L [(u, u + 8 * uc)]

/-- **`nat.div`** (amd64) as `(*Int).QuoRem` calls it from `(*Int).Mod`: `nil.div(nil, u, u, v)` (owner: top) -/
def DivHypM (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (u ul uc : BitVec 64) (v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program ExpHyp.fnDiv)
      [0#64, 0#64, 0#64, 0#64, u, ul, uc]
      (fun s => DivPreM R b cost L stk above u.toNat ul.toNat uc.toNat v vl vc s)
      (fun s s' => DivPostM R b cost L stk above u.toNat ul.toNat uc.toNat v vl s s')

end FvModexp.Amd64.IMod
