import Extracted
import FvModexp.Proofs.Arm64.Div64Sum

/-!
# Row: `math/bits.Div64(hi, lo, y uint64) (quo, rem uint64)` (arm64, Go ABIInternal, software 128/64 division)

**Guarantee** (`correctness`). For every call with `y != 0` and `hi < y` (the non-panicking domain of Go's
`bits.Div64`), a stack with room for the 40-byte frame and the stack-guard prologue passing (`GuardOK s 0`,
`StackOK s 40 0`), the call returns (no fault, no panic), restores `SP`, `g`, `FP`, `R18`, and returns in `X0, X1`
`quo = (hi * 2^64 + lo) / y` and `rem = (hi * 2^64 + lo) % y`; memory changes only in `[SP-40, SP-24)` (its frame).

It is the library summary `Div64Sum.ensures` (adapted from fv-uint256's `Div64` proof, retargeted to the pinned
go1.26.10 build) specialised to this extraction (same segment bytes, by `rfl`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace FvModexp.Arm64.Div64

theorem correctness (hi lo y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [hi, lo, y]
      (fun s => GuardOK s 0 ∧ StackOK s 40 0 ∧ y.toNat ≠ 0 ∧ hi.toNat < y.toNat)
      (fun s s' => results 2 s' =
          [BitVec.ofNat 64 ((hi.toNat * 2 ^ 64 + lo.toNat) / y.toNat),
           BitVec.ofNat 64 ((hi.toNat * 2 ^ 64 + lo.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 40, s.sp.toNat - 24)]) :=
  FvModexp.Arm64.Div64Sum.ensures hi lo y

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def hi : BitVec 64 := 2
def lo : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 1)
def y : BitVec 64 := 3

def s0 : State :=
  { regs := fun i => if i = 0 then hi else if i = 1 then lo else if i = 2 then y else if i = 30 then BitVec.ofNat 64 ret else if i = 28 then BitVec.ofNat 64 g0 else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x20, false⟩]⟩ }


theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [hi, lo, y] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 40 0 ∧ y.toNat ≠ 0 ∧ hi.toNat < y.toNat := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, by decide⟩

/-- A concrete call (`hi = 2`, `lo = 2^64 - 1`, `y = 3`: quotient `2^64 - 1`, remainder `2`) satisfies every
hypothesis of `correctness` and returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (hi lo y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [hi, lo, y] s ∧
    (GuardOK s 0 ∧ StackOK s 40 0 ∧ y.toNat ≠ 0 ∧ hi.toNat < y.toNat) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧
        (results 2 s' =
          [BitVec.ofNat 64 ((hi.toNat * 2 ^ 64 + lo.toNat) / y.toNat),
           BitVec.ofNat 64 ((hi.toNat * 2 ^ 64 + lo.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 40, s.sp.toNat - 24)])) :=
  ⟨ret, s0, hi, lo, y, hret, setup, hpre, correctness hi lo y ret hret s0 setup hpre⟩

end Witness

end FvModexp.Arm64.Div64
