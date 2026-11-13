import FvModexp.Proofs.Amd64.Int.ModDivHyp
import FvModexp.Proofs.Amd64.Int.LibQR
import FvModexp.Proofs.Amd64.Int.LibMod

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64) as `(*Int).Mod` calls it: the summary statement `IMod.QRSpec` (agent divmc)

On amd64 `QuoRem` is NOT inlined into `Mod` (arm64 inlines it): `z.Mod(z, y)` (int.go:325) calls
`q.QuoRem(x = z, y, r = z)` (int.go:331; `RAX = &q`, `RBX = x = z`, `RCX = y`, `RDI = r = z`, call at `Mod+0x212`),
with `q` the zeroed `var q Int` of `Mod`'s frame at `RSP + 96` (`RSP` = `QuoRem`'s entry `RSP`). `QuoRem`
(int.go:299-302; frame `0x68`) calls `q.abs.div(nil, r.abs, x.abs, y.abs)` (`QuoRem+0x87`; `stk == nil`, `z = q.abs =
nil`, `z2 = r.abs = u = x.abs`; premise `IMod.DivHypM`), stores `q.abs` (the pointer through `gcWriteBarrier4`,
`QuoRem+0xc0`, when the barrier is on) and `r.abs = z.abs`, `q.neg` (any byte) and `r.neg = len r > 0 && x.neg`
(`= 0`: `x.neg = z.neg = 0` by `IntOK`), and returns `RAX = &q`.

`QRPre` = `RunIface.ModSpec`'s precondition at `QuoRem`'s entry plus `q`'s place and zero header and `hasADX`
readable (`nat.div`'s pre since asm s48); `QRPost` = `ModSpec`'s
postcondition with `RAX = q`. The summary lives on `LibQR` (= `LibMod` without `Mod`, NESTED-PROGRAM RULE: `Mod`'s
return address `Mod+0x217` is outside it).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe maxW ModBudget lenW PoolG ModX)

/-- `QuoRem`'s precondition as `Mod` calls it (`s` = `QuoRem`'s entry state; `q` at `RSP + 96`, zero header) -/
def QRPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat) (q z y : Nat) (s : State) : Prop :=
  IntPre R b (ModBudget (max (lenW s.mem z) (lenW s.mem y))) L stk above [z, y] s ∧ 0 < IntV s.mem y ∧
    IntLenLe s.mem z maxW ∧ IntLenLe s.mem y maxW ∧ PoolG R s.mem (win s stk above) ∧ ModX s.mem z ∧
    q = (s.regs 4).toNat + 96 ∧ s.mem.readLE (q + 8) 8 = 0 ∧ s.mem.readLE (q + 16) 8 = 0 ∧
    s.mem.readLE (q + 24) 8 = 0 ∧ s.mem.accessible Callees.adxAddr 1 false = true

/-- `QuoRem`'s postcondition there: `RAX = q`, `z = z mod y` (`IntPost`; `q`'s header is in the window), `y` kept -/
def QRPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat) (q z y : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = BitVec.ofNat 64 q ∧
    IntPost R b (ModBudget (max (lenW s.mem z) (lenW s.mem y))) L stk above z (IntV s.mem z % IntV s.mem y) s s' ∧
    IntV s'.mem y = IntV s.mem y

/-- **`q.QuoRem(z, y, z)`** (amd64) as `(*Int).Mod` calls it, on `LibQR` -/
def QRSpec (impl : List Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (q z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments LibQR.names).link impl)
      (segAddr Extracted.program (RunIface.P ++ "(*Int).QuoRem")) [q, z, y, z]
      (fun s => QRPre R b L stk above q.toNat z.toNat y.toNat s)
      (fun s s' => QRPost R b L stk above q.toNat z.toNat y.toNat s s')

/-- `QuoRem`'s entry -/
@[reducible] def fnQ : Nat := 0x5e2b40

/-- `nat.div`'s entry -/
@[reducible] def fnD : Nat := 0x5edf20

/-- the return address of `QuoRem`'s `nat.div` call -/
@[reducible] def raD : Nat := 0x5e2bcc

theorem fnQ_eq : segAddr Extracted.program (RunIface.P ++ "(*Int).QuoRem") = fnQ := by decide

theorem fnD_eq : segAddr Extracted.program ExpHyp.fnDiv = fnD := by decide

end FvModexp.Amd64.IMod
