-- LEGACY (retired from the release, coordinator 2026-11-15): standalone row on the single-function extraction of `RecipWord`; its Run-extraction coverage is `Proofs/Arm64/RecipWordSum.lean` via the rows in docs/COVERAGE.md "Legacy standalone rows". Run on demand: scripts/asm-row.sh.
import Extracted
import FvModexp.Proofs.Arm64.RecipWordSum

/-!
# Row: `math/big.reciprocalWord(d1 Word) Word` (go-bigmodexpfix arith.go:333, arm64, Go ABIInternal)

**Guarantee** (`correctness`). For every call with `d1 != 0`, the stack guard below `SP - 48` and 88 writable bytes
below `SP` (its frame and the frame of the callee `math/bits.Div64`), the guard word apart from that area: the call
returns (no fault, no panic, no `morestack`), restores `SP`, `g`, `FP`, `R18`, and returns in `X0`
`recipWord d1 = floor((2^128 - 1) / (d1 << nlz d1)) - 2^64` (the reciprocal `divWW` takes); memory changes only in the
bytes `[SP - 88, SP - 40)`. Library summary: `RecipWordSum.ensures` (the extraction of this row is the library program,
`reciprocalWord` + `Div64` and their stubs).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace FvModexp.Arm64.RecipWord

theorem correctness (d1 : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d1]
      (fun s => GuardOK s 48 ∧ StackOK s 88 0 ∧ d1.toNat ≠ 0 ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 88)
      (fun s s' => results 1 s' =
          [BitVec.ofNat 64 ((2 ^ 128 - 1) / (d1.toNat * 2 ^ clzNat 64 d1.toNat) - 2 ^ 64)] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat - 40)]) :=
  FvModexp.Arm64.RecipWordSum.ensures d1

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000

def d1 : BitVec 64 := 3

def s0 : State :=
  { regs := fun i => if i = 0 then d1 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x40, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [d1] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0) with rfl; rfl⟩

theorem hpre : GuardOK s0 48 ∧ StackOK s0 88 0 ∧ d1.toNat ≠ 0 ∧
    Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 88) 88 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, by unfold Apart; decide⟩

/-- A concrete call (`d1 = 3`, `nlz = 62`) satisfies the hypotheses of `correctness` and returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (d1 : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [d1] s ∧
    (GuardOK s 48 ∧ StackOK s 88 0 ∧ d1.toNat ≠ 0 ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 88) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧
        (results 1 s' = [BitVec.ofNat 64 ((2 ^ 128 - 1) / (d1.toNat * 2 ^ clzNat 64 d1.toNat) - 2 ^ 64)] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat - 40)])) :=
  ⟨ret, s0, d1, hret, setup, hpre, correctness d1 ret hret s0 setup hpre⟩

end Witness

end FvModexp.Arm64.RecipWord
