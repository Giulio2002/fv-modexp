import Extracted
import FvModexp.Proofs.Arm64.CmpSum

/-!
# Row: `math/big.nat.cmp(x, y nat) (r int)` (go-bigmodexpfix nat.go:152-180, Go ABIInternal, arm64)

**Guarantee** (`correctness`). For every call with `x = (X0, X1, X2)`, `y = (X3, X4, X5)`, the stack guard passing and
the frame window `[SP-24, SP+40)` writable, each slice empty or readable and outside that window: the call returns (no
fault, no bounds panic, every length), restores `SP`, `g`, `FP`, `R18`, and returns in `X0` the Go `int` `-1`/`0`/`1`
(as a 64-bit word): lengths first (`len(x) < len(y)` gives `-1`), then for equal lengths the comparison of the values
`readLE x (8 len)` and `readLE y (8 len)`; memory changes only in its frame record and the two argument spill slots.
The library summary `CmpSum.cmp_summary` (and its model form `AsmModels.cmp_res_model`: `X0 = Mdl.natCmp x y`)
specialised to this extraction.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace FvModexp.Arm64.Cmp

theorem correctness (x xl xc y yl yc : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, xl, xc, y, yl, yc]
      (fun s => GuardOK s 0 ∧ StackOK s 24 40 ∧
        (xl.toNat = 0 ∨ (s.mem.accessible x.toNat (8 * xl.toNat) false = true ∧
          Apart x.toNat (8 * xl.toNat) (s.sp.toNat - 24) 64)) ∧
        (yl.toNat = 0 ∨ (s.mem.accessible y.toNat (8 * yl.toNat) false = true ∧
          Apart y.toNat (8 * yl.toNat) (s.sp.toNat - 24) 64)))
      (fun s s' => results 1 s' =
          [if xl.toNat < yl.toNat then 18446744073709551615#64 else if yl.toNat < xl.toNat then 1#64
            else if s.mem.readLE x.toNat (8 * xl.toNat) < s.mem.readLE y.toNat (8 * yl.toNat) then 18446744073709551615#64
            else if s.mem.readLE y.toNat (8 * yl.toNat) < s.mem.readLE x.toNat (8 * xl.toNat) then 1#64 else 0#64] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16),
          (s.sp.toNat + 32, s.sp.toNat + 40)]) :=
  FvModexp.Arm64.CmpSum.ensures x xl xc y yl yc

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : Nat := 0x300000

def bytes (a : Nat) : Byte :=
  if a = dat then 5 else if a = dat + 8 then 7 else if a = dat + 0x40 then 5 else if a = dat + 0x48 then 9 else 0

def x : BitVec 64 := BitVec.ofNat 64 dat
def y : BitVec 64 := BitVec.ofNat 64 (dat + 0x40)

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 1 then 2 else if i = 2 then 2 else if i = 3 then y
      else if i = 4 then 2 else if i = 5 then 2 else if i = 30 then BitVec.ofNat 64 ret
      else if i = 28 then BitVec.ofNat 64 g0 else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x20, false⟩, ⟨dat, 0x100, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, 2, 2, y, 2, 2] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 24 40 ∧
    ((2 : BitVec 64).toNat = 0 ∨ (s0.mem.accessible x.toNat (8 * (2 : BitVec 64).toNat) false = true ∧
      Apart x.toNat (8 * (2 : BitVec 64).toNat) (s0.sp.toNat - 24) 64)) ∧
    ((2 : BitVec 64).toNat = 0 ∨ (s0.mem.accessible y.toNat (8 * (2 : BitVec 64).toNat) false = true ∧
      Apart y.toNat (8 * (2 : BitVec 64).toNat) (s0.sp.toNat - 24) 64)) := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, Or.inr ⟨by decide, by unfold Apart; decide⟩,
    Or.inr ⟨by decide, by unfold Apart; decide⟩⟩

/-- A concrete call (`x = [5, 7]`, `y = [5, 9]`: equal lengths, the loop runs, `x < y`) satisfies every hypothesis of
`correctness` and returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x xl xc y yl yc : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, xl, xc, y, yl, yc] s ∧
    (GuardOK s 0 ∧ StackOK s 24 40 ∧
        (xl.toNat = 0 ∨ (s.mem.accessible x.toNat (8 * xl.toNat) false = true ∧
          Apart x.toNat (8 * xl.toNat) (s.sp.toNat - 24) 64)) ∧
        (yl.toNat = 0 ∨ (s.mem.accessible y.toNat (8 * yl.toNat) false = true ∧
          Apart y.toNat (8 * yl.toNat) (s.sp.toNat - 24) 64))) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧
        (results 1 s' =
          [if xl.toNat < yl.toNat then 18446744073709551615#64 else if yl.toNat < xl.toNat then 1#64
            else if s.mem.readLE x.toNat (8 * xl.toNat) < s.mem.readLE y.toNat (8 * yl.toNat) then 18446744073709551615#64
            else if s.mem.readLE y.toNat (8 * yl.toNat) < s.mem.readLE x.toNat (8 * xl.toNat) then 1#64 else 0#64] ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16),
          (s.sp.toNat + 32, s.sp.toNat + 40)])) :=
  ⟨ret, s0, x, 2, 2, y, 2, 2, hret, setup, hpre, correctness x 2 2 y 2 2 ret hret s0 setup hpre⟩

end Witness

end FvModexp.Arm64.Cmp
