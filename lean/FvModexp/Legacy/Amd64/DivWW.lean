-- LEGACY (retired from the release, coordinator 2026-11-15): standalone row on the single-function extraction of `DivWW`; its Run-extraction coverage is `Proofs/Amd64/DivWWSum.lean` via the rows in docs/COVERAGE.md "Legacy standalone rows". Run on demand: scripts/asm-row.sh.
import Extracted
import FvModexp.Proofs.Amd64.DivWWSum

/-!
# Row: `math/big.divWW(x1, x0, y, m Word) (q, r Word)` (go-bigmodexpfix arith.go:273, amd64, Go ABIInternal)

**Guarantee** (`correctness`). For every call with `y != 0`, `x1 < y` and `m = floor((2^128-1) / (y << nlz y)) - 2^64`
(`nlz` = leading zero bits; the value `reciprocalWord(y)` returns), the call returns (no fault, no panic, frameless, no stack
check; the return-address slot readable), restores `RSP`, `RBP`, `g` (`R14`), `X15`, and returns in `RAX, RBX` the quotient `(x1 * 2^64 + x0) / y` and the remainder
`(x1 * 2^64 + x0) % y`; memory is unchanged.  Library summary: `DivWWSum.ensures`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

namespace FvModexp.Amd64.DivWW

theorem correctness (x1 x0 y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x1, x0, y, m]
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧ y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
        m.toNat = (2 ^ 128 - 1) / (y.toNat * 2 ^ Janus.Arm64.clzNat 64 y.toNat) - 2 ^ 64)
      (fun s s' => results 2 s' =
          [BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) / y.toNat),
           BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem []) :=
  FvModexp.Amd64.DivWWSum.ensures x1 x0 y m

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000

def x1 : BitVec 64 := 1
def x0 : BitVec 64 := 5
def y : BitVec 64 := 3
def m : BitVec 64 := 6148914691236517205

def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else 0

def s0 : State :=
  { regs := fun i => if i = 0 then x1 else if i = 3 then x0 else if i = 1 then y else if i = 7 then m
      else if i = 4 then BitVec.ofNat 64 sp0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x1, x0, y, m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl,
   rfl⟩

theorem hpre : s0.mem.accessible (s0.regs 4).toNat 8 false = true ∧ y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
    m.toNat = (2 ^ 128 - 1) / (y.toNat * 2 ^ Janus.Arm64.clzNat 64 y.toNat) - 2 ^ 64 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- A concrete call (`x1 = 1`, `x0 = 5`, `y = 3`, `m` the reciprocal of `y`: the shifted path, `nlz y = 62`) satisfies
the hypotheses of `correctness` and returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x1 x0 y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x1, x0, y, m] s ∧
    (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
        m.toNat = (2 ^ 128 - 1) / (y.toNat * 2 ^ Janus.Arm64.clzNat 64 y.toNat) - 2 ^ 64) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧
        (results 2 s' =
          [BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) / y.toNat),
           BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem [])) :=
  ⟨ret, s0, x1, x0, y, m, hret, setup, hpre, correctness x1 x0 y m ret hret s0 setup hpre⟩

end Witness

end FvModexp.Amd64.DivWW
