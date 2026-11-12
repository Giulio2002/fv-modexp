import FvModexp.Proofs.Amd64.Int.LibIntAS
import FvModexp.Proofs.Amd64.Nat.NatAddDefs
import FvModexp.Proofs.Amd64.Nat.NatSubDefs
import FvModexp.Proofs.Amd64.Nat.DivmcCall
import FvModexp.Proofs.Amd64.CmpSum
import FvModexp.Proofs.Amd64.Top.RunIface

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (go-bigmodexpfix int.go:141 / int.go:162), amd64 — statement and shared lemmas

Twin of `FvModexp.Arm64.IntAS` (see there for the Go source). The two functions are the same machine code (`Add` at
`0x5e2620`, `Sub` at `0x5e2800`, every offset equal) except for the first branch (`JNE` / `JEQ` after
`CMPB 0(CX), DL` on `x.neg` vs `y.neg`). Frame: `PUSHQ BP; SUBQ $0x50, SP` (`RSP' = RSP - 88`), spills `z` at
`0x60(RSP') = RSP + 8`, `x`/`y` at `RSP + 16`/`RSP + 24` (`above = 32`), `neg` at `0x4f(RSP') = RSP - 9`. The callees
(`nat.add`, window 4440; `nat.sub`, 4288; `nat.cmp`) run at `RSP - 96`: `stk = 96 + 4440 = 4536`. Arguments
`z = AX`, `x = BX`, `y = CX` (`regs 0, 3, 1`); result `AX`. Unlike arm64, each of the three call sites has its own
copy of the tail (`z.abs = …` with the write barrier `gcWriteBarrier2`; `z.neg = len > 0 && neg`; epilogue).
`*Int` header: `neg` byte at `+0`, `abs = (ptr, len, cap)` at `+8, +16, +24`. Signs are general (`neg ∈ {0, 1}`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.IntAS

open FvModexp.Amd64.RunIface (Serves)

def fnAdd : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add"
def fnSub : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub"
def names : List String := LibIntAS.names

/-- the function (`sub = false`: `Add`, `true`: `Sub`) -/
def fn (sub : Bool) : String := if sub then fnSub else fnAdd

/-- the entry address of the function -/
def entry (sub : Bool) : Nat := if sub then 0x5e2800 else 0x5e2620

theorem entry_eq (sub : Bool) : segAddr Extracted.program (fn sub) = entry sub := by
  cases sub <;> decide

/-- `runtime.writeBarrier`'s flag word -/
abbrev wbA : Nat := Extracted.dataAddr.«runtime.writeBarrier»

/-! ## The `*Int` header (as the arm64 twin) -/

@[reducible] def hNeg (m : Arm64.Memory) (a : Nat) : Nat := m.readLE a 1
@[reducible] def hP (m : Arm64.Memory) (a : Nat) : Nat := m.readLE (a + 8) 8
@[reducible] def hL (m : Arm64.Memory) (a : Nat) : Nat := m.readLE (a + 16) 8
@[reducible] def hC (m : Arm64.Memory) (a : Nat) : Nat := m.readLE (a + 24) 8

/-- the signed value of the `*Int` at `a` (`neg = 0`: `|x|`, else `-|x|`) -/
def intZ (m : Arm64.Memory) (a : Nat) : Int :=
  if hNeg m a = 0 then (natVal m (hP m a) (hL m a) : Int) else -(natVal m (hP m a) (hL m a) : Int)

/-- the result of `x + y` (`sub = false`) / `x - y` (`sub = true`) -/
def resZ (sub : Bool) (vx vy : Int) : Int := if sub then vx - vy else vx + vy

/-- the budget: `nat.add` or `nat.sub` (`makeCap 0 = 4 > makeCap 1`, hence the max) -/
def asCost (xl yl : Nat) : Nat := max (makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1)) (makeCost (max xl yl))

/-- the capacity of `z.abs` that `nat.add` / `nat.sub` keep -/
def asNeed (xl yl : Nat) : Nat := if min xl yl = 0 then max xl yl else max xl yl + 1

/-- a read-only `*Int` operand: header readable outside the window, `neg ∈ {0, 1}`, `abs` normalised, readable,
held and outside the window -/
@[reducible] def OpR (R : RtInv) (L : List (Nat × Nat)) (s : State) (a : Nat) : Prop :=
  hNeg s.mem a ≤ 1 ∧ s.mem.accessible a 32 false = true ∧ a + 32 ≤ 2 ^ 48 ∧ Outside a 32 (win s 4536 32) ∧
    hL s.mem a ≤ hC s.mem a ∧ hC s.mem a < 2 ^ 40 ∧ hL s.mem a ≤ 2 ^ 16 ∧
    s.mem.accessible (hP s.mem a) (8 * hL s.mem a) false = true ∧ hP s.mem a + 8 * hL s.mem a ≤ 2 ^ 48 ∧
    Held R L (hP s.mem a) (8 * hL s.mem a) ∧ NatNorm s.mem (hP s.mem a) (hL s.mem a) ∧
    Outside (hP s.mem a) (8 * hL s.mem a) (win s 4536 32)

/-- The precondition (both functions; args `AX = z`, `BX = x`, `CX = y`). `z` may be `x` (`z1.Add(z1, z0)`). As the
arm64 twin, plus the TLS slot `fsBase - 8` apart from what is written (`z`'s header and old array). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) : Prop :=
  CallEnv R L s 4536 32 ∧ Serves R ∧ Outside NatAdd.wordT 16 R.rt ∧ OpR R L s x ∧ OpR R L s y ∧
    s.mem.accessible z 32 true = true ∧ z + 32 ≤ 2 ^ 48 ∧ Outside z 32 (win s 4536 32) ∧ Held R L z 32 ∧
    Apart z 32 ((s.regs 14).toNat + 16) 8 ∧ Apart z 32 (s.fsBase.toNat - 8) 8 ∧ Apart z 32 wbA 4 ∧
    (z = x ∨ Apart z 32 x 32) ∧ Apart z 32 y 32 ∧
    hC s.mem z < 2 ^ 40 ∧ NatLive s.mem R L (hP s.mem z) (hC s.mem z) ∧
    Outside (hP s.mem z) (8 * hC s.mem z) (win s 4536 32) ∧
    (0 < hC s.mem z → Apart (hP s.mem z) (8 * hC s.mem z) ((s.regs 14).toNat + 16) 8 ∧
      Apart (hP s.mem z) (8 * hC s.mem z) (s.fsBase.toNat - 8) 8 ∧
      Apart (hP s.mem z) (8 * hC s.mem z) z 32 ∧
      (hP s.mem z = hP s.mem x ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem x) (8 * hL s.mem x)) ∧
      (hP s.mem z = hP s.mem y ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem y) (8 * hL s.mem y))) ∧
    s.mem.accessible wbA 4 false = true ∧ asCost (hL s.mem x) (hL s.mem y) ≤ b ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- The postcondition (as the arm64 twin, plus `fsBase`/`DF` unchanged — AMD64 DF CONVENTION): `z` (returned in
`AX`) holds `x ± y` with a canonical sign, a normalised `abs` in `z`'s old array (always when its capacity suffices)
or a fresh one; writes only `z`'s header, `z`'s old array, `R.rt` and the window. -/
def Post (sub : Bool) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  s'.regs 0 = BitVec.ofNat 64 z ∧ intZ s'.mem z = resZ sub (intZ s.mem x) (intZ s.mem y) ∧
    hNeg s'.mem z ≤ 1 ∧ (hNeg s'.mem z = 1 → 0 < hL s'.mem z) ∧ NatNorm s'.mem (hP s'.mem z) (hL s'.mem z) ∧
    hL s'.mem z ≤ hC s'.mem z ∧ hL s'.mem z ≤ max (hL s.mem x) (hL s.mem y) + 1 ∧ hC s'.mem z < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - asCost (hL s.mem x) (hL s.mem y) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' (hP s'.mem z) (hC s'.mem z) ∧
      ((hP s'.mem z = hP s.mem z ∧ hC s'.mem z = hC s.mem z) ∨
        (InRanges (hP s'.mem z) (8 * hC s'.mem z) R.rt ∧ ApartAll (hP s'.mem z) (8 * hC s'.mem z) L)) ∧
      (asNeed (hL s.mem x) (hL s.mem y) ≤ hC s.mem z → hP s'.mem z = hP s.mem z ∧ hC s'.mem z = hC s.mem z) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4536 32 ++ [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))]) ∧
      LiveFrame s.mem s'.mem L [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))]

/-! ## Small helpers -/

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- a fact hidden from `janus64_run` (which destructures every conjunction in the context: slow) -/
structure Box (P : Prop) : Prop where
  h : P

theorem asCost_add (xl yl : Nat) : makeCost (asNeed xl yl) ≤ asCost xl yl := by
  unfold asCost asNeed; exact Nat.le_max_left _ _

theorem asCost_sub (xl yl : Nat) : makeCost (max xl yl) ≤ asCost xl yl := by
  unfold asCost; exact Nat.le_max_right _ _

end FvModexp.Amd64.IntAS
