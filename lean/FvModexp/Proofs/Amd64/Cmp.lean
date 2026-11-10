import Extracted
import FvModexp.Proofs.Amd64.CmpSum

/-!
# Row: `math/big.nat.cmp(x, y nat) (r int)` (go-bigmodexpfix nat.go:152-180, Go ABIInternal, amd64)

**Guarantee** (`correctness`). For every call with `x = (RAX, RBX, RCX)`, `y = (RDI, RSI, R8)` and the stack window
`[RSP-8, RSP+40)` writable (no stack-growth prologue: the function has no call but the bounds panic), each slice empty or readable and outside that window: the call returns (no
fault, no bounds panic, every length), pops the return address, restores `RBP`, `R14`, `X15`, and returns in `RAX` the Go `int` `-1`/`0`/`1`
(as a 64-bit word): lengths first (`len(x) < len(y)` gives `-1`), then for equal lengths the comparison of the values
`readLE x (8 len)` and `readLE y (8 len)`; memory changes only in its saved `RBP` slot and the two argument spill slots.
The library summary `CmpSum.cmp_summary` 
specialised to this extraction.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

namespace FvModexp.Amd64.Cmp

theorem correctness (x xl xc y yl yc : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, xl, xc, y, yl, yc]
      (fun s => 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat - 8) 48 true = true ∧
        (xl.toNat = 0 ∨ (s.mem.accessible x.toNat (8 * xl.toNat) false = true ∧
          Apart x.toNat (8 * xl.toNat) ((s.regs 4).toNat - 8) 48)) ∧
        (yl.toNat = 0 ∨ (s.mem.accessible y.toNat (8 * yl.toNat) false = true ∧
          Apart y.toNat (8 * yl.toNat) ((s.regs 4).toNat - 8) 48)))
      (fun s s' => results 1 s' =
          [if xl.toNat < yl.toNat then 18446744073709551615#64 else if yl.toNat < xl.toNat then 1#64
            else if s.mem.readLE x.toNat (8 * xl.toNat) < s.mem.readLE y.toNat (8 * yl.toNat) then 18446744073709551615#64
            else if s.mem.readLE y.toNat (8 * yl.toNat) < s.mem.readLE x.toNat (8 * xl.toNat) then 1#64 else 0#64] ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16),
          ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)]) :=
  FvModexp.Amd64.CmpSum.ensures x xl xc y yl yc

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def dat : Nat := 0x300000

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = dat then 5 else if a = dat + 8 then 7 else if a = dat + 0x40 then 5 else if a = dat + 0x48 then 9 else 0

def x : BitVec 64 := BitVec.ofNat 64 dat
def y : BitVec 64 := BitVec.ofNat 64 (dat + 0x40)

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then 2 else if i = 1 then 2 else if i = 7 then y
      else if i = 6 then 2 else if i = 8 then 2 else if i = 4 then BitVec.ofNat 64 sp0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨dat, 0x100, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, 2, 2, y, 2, 2] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl,
   rfl⟩

theorem hpre : 8 ≤ (s0.regs 4).toNat ∧ (s0.regs 4).toNat + 40 ≤ 2 ^ 48 ∧
    s0.mem.accessible ((s0.regs 4).toNat - 8) 48 true = true ∧
    ((2 : BitVec 64).toNat = 0 ∨ (s0.mem.accessible x.toNat (8 * (2 : BitVec 64).toNat) false = true ∧
      Apart x.toNat (8 * (2 : BitVec 64).toNat) ((s0.regs 4).toNat - 8) 48)) ∧
    ((2 : BitVec 64).toNat = 0 ∨ (s0.mem.accessible y.toNat (8 * (2 : BitVec 64).toNat) false = true ∧
      Apart y.toNat (8 * (2 : BitVec 64).toNat) ((s0.regs 4).toNat - 8) 48)) := by
  refine ⟨by decide, by decide, by decide, Or.inr ⟨by decide, by unfold Apart; decide⟩,
    Or.inr ⟨by decide, by unfold Apart; decide⟩⟩

/-- A concrete call (`x = [5, 7]`, `y = [5, 9]`: equal lengths, the loop runs, `x < y`) satisfies every hypothesis of
`correctness` and returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x xl xc y yl yc : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, xl, xc, y, yl, yc] s ∧
    (8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat - 8) 48 true = true ∧
        (xl.toNat = 0 ∨ (s.mem.accessible x.toNat (8 * xl.toNat) false = true ∧
          Apart x.toNat (8 * xl.toNat) ((s.regs 4).toNat - 8) 48)) ∧
        (yl.toNat = 0 ∨ (s.mem.accessible y.toNat (8 * yl.toNat) false = true ∧
          Apart y.toNat (8 * yl.toNat) ((s.regs 4).toNat - 8) 48))) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧
        (results 1 s' =
          [if xl.toNat < yl.toNat then 18446744073709551615#64 else if yl.toNat < xl.toNat then 1#64
            else if s.mem.readLE x.toNat (8 * xl.toNat) < s.mem.readLE y.toNat (8 * yl.toNat) then 18446744073709551615#64
            else if s.mem.readLE y.toNat (8 * yl.toNat) < s.mem.readLE x.toNat (8 * xl.toNat) then 1#64 else 0#64] ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16),
          ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)])) :=
  ⟨ret, s0, x, 2, 2, y, 2, 2, hret, setup, hpre, correctness x 2 2 y 2 2 ret hret s0 setup hpre⟩

end Witness

end FvModexp.Amd64.Cmp
