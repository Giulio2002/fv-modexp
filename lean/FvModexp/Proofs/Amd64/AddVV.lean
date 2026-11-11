import Extracted
import FvModexp.Proofs.Amd64.AddVVSum

/-!
# Row: `math/big.addVV.abi0` (go-bigmodexpfix arith_amd64.s, Go assembly, ABI0, amd64)

**Guarantee** (`correctness`). For every ABI0 call of `addVV(z, x, y []Word) (c Word)` (frame words
`z, len(z), cap(z), x, len(x), cap(x), y, len(y), cap(y)`, result word 9) with `n = len(z)` and
`z[0:n]` writable, `x[0:n]`, `y[0:n]` readable, `z` equal to or disjoint from each of `x` and `y`, and `z[0:n]` disjoint
from the call frame (return address, argument and result words): the call returns (no fault, every length `n`), pops the return address (`RSP` + 8), restores `RBP`, the `FS` base and `DF`, and

* the `n` limbs at `z` hold `(X + Y) mod 2^(64 n)`, where `X`, `Y` are the values `Σ limb_i·2^(64 i)` of `x[0:n]`,
  `y[0:n]` before the call (`readLE p (8 n)` is that little-endian value);
* the result word is the carry `(X + Y) / 2^(64 n)`;
* nothing outside `z[0:n]` and the result word changes.

It is the library summary `AddVVSum.addVV_summary` (proved on the Extracted-free library program, which callers
use through `CodeIn`) specialised to this extraction (the same single segment, by `rfl`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec

namespace FvModexp.Amd64.AddVV

theorem correctness (z zl zc x xl xc y yl yc : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 88)
      (fun s s' =>
        s'.mem.readLE z.toNat (8 * zl.toNat) =
          (s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat)) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 9 1 =
          [BitVec.ofNat 64 ((s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat)) /
            2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]) :=
  FvModexp.Amd64.AddVVSum.ensures z zl zc x xl xc y yl yc

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def dat : Nat := 0x300000

/-- the 64-bit words of the witness memory (little-endian), all other bytes `0` -/
def words : List (Nat × Nat) :=
  [(sp0, ret), (sp0 + 8, dat), (sp0 + 16, 1), (sp0 + 24, 1), (sp0 + 32, dat + 0x40), (sp0 + 40, 1), (sp0 + 48, 1),
   (sp0 + 56, dat + 0x80), (sp0 + 64, 1), (sp0 + 72, 1), (dat + 0x40, 2 ^ 64 - 1), (dat + 0x80, 7)]

def bytes (a : Nat) : Byte :=
  match words.find? (fun w => w.1 ≤ a && a < w.1 + 8) with
  | some (b, v) => BitVec.ofNat 8 (v / 2 ^ (8 * (a - b)))
  | none => 0

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨dat, 0x100, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def args : List (BitVec 64) := [BitVec.ofNat 64 dat, 1, 1, BitVec.ofNat 64 (dat + 0x40), 1, 1,
  BitVec.ofNat 64 (dat + 0x80), 1, 1]

theorem setup : CallSetup0 (Extracted.program.withExit ret) Extracted.entry args 1 s0 :=
  ⟨rfl, by decide, by
    intro i h
    simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [args, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide,
   ⟨by decide, by decide⟩, rfl⟩

theorem hpre : (fun s : State => Ptr s.mem (BitVec.ofNat 64 dat) (8 * (1 : BitVec 64).toNat) true ∧
    Ptr s.mem (BitVec.ofNat 64 (dat + 0x40)) (8 * (1 : BitVec 64).toNat) false ∧
    Ptr s.mem (BitVec.ofNat 64 (dat + 0x80)) (8 * (1 : BitVec 64).toNat) false ∧
    ((BitVec.ofNat 64 dat : BitVec 64).toNat = (BitVec.ofNat 64 (dat + 0x40) : BitVec 64).toNat ∨
      Apart (BitVec.ofNat 64 dat : BitVec 64).toNat (8 * (1 : BitVec 64).toNat)
        (BitVec.ofNat 64 (dat + 0x40) : BitVec 64).toNat (8 * (1 : BitVec 64).toNat)) ∧
    ((BitVec.ofNat 64 dat : BitVec 64).toNat = (BitVec.ofNat 64 (dat + 0x80) : BitVec 64).toNat ∨
      Apart (BitVec.ofNat 64 dat : BitVec 64).toNat (8 * (1 : BitVec 64).toNat)
        (BitVec.ofNat 64 (dat + 0x80) : BitVec 64).toNat (8 * (1 : BitVec 64).toNat)) ∧
    Apart (BitVec.ofNat 64 dat : BitVec 64).toNat (8 * (1 : BitVec 64).toNat) (s.regs 4).toNat 88) s0 := by
  simp only [Ptr, Apart]; decide

/-- All the hypotheses of `correctness` hold together at a concrete call (`n = 1`, `x[0] = 2^64 - 1`, `y[0] = 7`:
a carry out), and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z zl zc x xl xc y yl yc : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc] 1 s ∧
    (Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 88) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn0 s s' ∧
        (s'.mem.readLE z.toNat (8 * zl.toNat) =
          (s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat)) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 9 1 =
          [BitVec.ofNat 64 ((s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat)) /
            2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)])) :=
  ⟨ret, s0, _, _, _, _, _, _, _, _, _, hret, setup, hpre,
    correctness _ _ _ _ _ _ _ _ _ ret hret s0 setup hpre⟩

end Witness

end FvModexp.Amd64.AddVV
