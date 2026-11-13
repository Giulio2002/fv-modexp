-- LEGACY (retired from the release, coordinator 2026-11-15): standalone row on the single-function extraction of `DivWW`; its Run-extraction coverage is `Proofs/Arm64/DivWWSum.lean` via the rows in docs/COVERAGE.md "Legacy standalone rows". Run on demand: scripts/asm-row.sh.
import Extracted
import FvModexp.Proofs.Arm64.DivWWSum

/-!
# Row: `math/big.divWW(x1, x0, y, m Word) (q, r Word)` (go-bigmodexpfix arith.go:273, arm64, Go ABIInternal)

**Guarantee** (`correctness`). For every call with `y != 0`, `x1 < y` and `m = floor((2^128-1) / (y << nlz y)) - 2^64`
(`nlz` = leading zero bits; the value `reciprocalWord(y)` returns), the call returns (no fault, no panic, frameless, no stack
check), restores `SP`, `g`, `FP`, `R18`, and returns in `X0, X1` the quotient `(x1 * 2^64 + x0) / y` and the remainder
`(x1 * 2^64 + x0) % y`; memory is unchanged.  Library summary: `DivWWSum.ensures`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace FvModexp.Arm64.DivWW

theorem correctness (x1 x0 y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x1, x0, y, m]
      (fun _ => y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
        m.toNat = (2 ^ 128 - 1) / (y.toNat * 2 ^ clzNat 64 y.toNat) - 2 ^ 64)
      (fun s s' => results 2 s' =
          [BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) / y.toNat),
           BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem []) :=
  FvModexp.Arm64.DivWWSum.ensures x1 x0 y m

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000

def x1 : BitVec 64 := 1
def x0 : BitVec 64 := 5
def y : BitVec 64 := 3
def m : BitVec 64 := 6148914691236517205

def s0 : State :=
  { regs := fun i => if i = 0 then x1 else if i = 1 then x0 else if i = 2 then y else if i = 3 then m
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 0x100, 0x200, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x1, x0, y, m] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
    m.toNat = (2 ^ 128 - 1) / (y.toNat * 2 ^ clzNat 64 y.toNat) - 2 ^ 64 := by
  refine ⟨by decide, by decide, by decide⟩

/-- A concrete call (`x1 = 1`, `x0 = 5`, `y = 3`, `m` the reciprocal of `y`: the shifted path, `nlz y = 62`) satisfies
the hypotheses of `correctness` and returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x1 x0 y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x1, x0, y, m] s ∧
    (y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
        m.toNat = (2 ^ 128 - 1) / (y.toNat * 2 ^ clzNat 64 y.toNat) - 2 ^ 64) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧
        (results 2 s' =
          [BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) / y.toNat),
           BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem [])) :=
  ⟨ret, s0, x1, x0, y, m, hret, setup, hpre, correctness x1 x0 y m ret hret s0 setup hpre⟩

end Witness

end FvModexp.Arm64.DivWW
