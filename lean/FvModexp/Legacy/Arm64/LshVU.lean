-- LEGACY (retired from the release, coordinator 2026-11-15): standalone row on the single-function extraction of `LshVU`; its Run-extraction coverage is `Proofs/Arm64/LshVUSum.lean` via the rows in docs/COVERAGE.md "Legacy standalone rows". Run on demand: scripts/asm-row.sh.
import Extracted
import FvModexp.Proofs.Arm64.LshVUSum

/-!
# Row: `math/big.lshVU.abi0` (go-bigmodexpfix arith_arm64.s, Go assembly, ABI0, arm64)

**Guarantee** (`correctness`). For every ABI0 call of `lshVU(z, x []Word, s uint) (c Word)` (frame words
`z, len(z), cap(z), x, len(x), cap(x), s`, result word 7) with `n = len(z)`, `z[0:n]` writable, `x[0:n]` readable,
`1 ≤ s ≤ 63`, `x ≤ z` or `x[0:n]` disjoint from `z[0:n]` (the loop runs backward), and both slices disjoint from the
result word: the call returns (no fault, every length `n`), restores `SP`, `g`, `FP`, `R18`, and

* the `n` limbs at `z` hold `(X · 2^s) mod 2^(64 n)` (`X` = the value of `x[0:n]` before the call);
* the result word is `(X · 2^s) / 2^(64 n)` (the bits shifted out);
* nothing outside `z[0:n]` and the result word changes.

It is the library summary `LshVUSum.lshVU_summary` specialised to this extraction (the same single segment).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm

namespace FvModexp.Arm64.LshVU

theorem correctness (z zl zc x xl xc sh : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [z, zl, zc, x, xl, xc, sh] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        1 ≤ sh.toNat ∧ sh.toNat ≤ 63 ∧
        (x.toNat ≤ z.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8 ∧ Apart x.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8)
      (fun s s' =>
        s'.mem.readLE z.toNat (8 * zl.toNat) = (s.mem.readLE x.toNat (8 * zl.toNat) * 2 ^ sh.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 7 1 =
          [BitVec.ofNat 64 ((s.mem.readLE x.toNat (8 * zl.toNat) * 2 ^ sh.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 64, s.sp.toNat + 72)]) :=
  FvModexp.Arm64.LshVUSum.ensures z zl zc x xl xc sh

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def dat : Nat := 0x300000

/-- the 64-bit words of the witness memory (little-endian), all other bytes `0` -/
def words : List (Nat × Nat) :=
  [(sp0 + 8, dat), (sp0 + 16, 1), (sp0 + 24, 1), (sp0 + 32, dat + 0x40), (sp0 + 40, 1), (sp0 + 48, 1),
   (sp0 + 56, 1), (dat + 0x40, 2 ^ 64 - 1)]

def bytes (a : Nat) : Byte :=
  match words.find? (fun w => w.1 ≤ a && a < w.1 + 8) with
  | some (b, v) => BitVec.ofNat 8 (v / 2 ^ (8 * (a - b)))
  | none => 0

def s0 : State :=
  { regs := fun i => if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨dat, 0x100, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def args : List (BitVec 64) := [BitVec.ofNat 64 dat, 1, 1, BitVec.ofNat 64 (dat + 0x40), 1, 1, 1]

theorem setup : CallSetup0 (Extracted.program.withExit ret) Extracted.entry args 1 s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [args, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide,
   ⟨by decide, by decide⟩, by decide⟩

theorem hpre : (fun s : State => Ptr s.mem (BitVec.ofNat 64 dat) (8 * (1 : BitVec 64).toNat) true ∧
    Ptr s.mem (BitVec.ofNat 64 (dat + 0x40)) (8 * (1 : BitVec 64).toNat) false ∧
    1 ≤ (1 : BitVec 64).toNat ∧ (1 : BitVec 64).toNat ≤ 63 ∧
    ((BitVec.ofNat 64 (dat + 0x40) : BitVec 64).toNat ≤ (BitVec.ofNat 64 dat : BitVec 64).toNat ∨
      Apart (BitVec.ofNat 64 dat : BitVec 64).toNat (8 * (1 : BitVec 64).toNat)
        (BitVec.ofNat 64 (dat + 0x40) : BitVec 64).toNat (8 * (1 : BitVec 64).toNat)) ∧
    Apart (BitVec.ofNat 64 dat : BitVec 64).toNat (8 * (1 : BitVec 64).toNat) (s.sp.toNat + 64) 8 ∧
    Apart (BitVec.ofNat 64 (dat + 0x40) : BitVec 64).toNat (8 * (1 : BitVec 64).toNat) (s.sp.toNat + 64) 8) s0 := by
  simp only [Ptr, Apart]; decide

/-- All the hypotheses of `correctness` hold together at a concrete call (`n = 1`, `x[0] = 2^64 - 1`, `s = 1`:
a bit shifted out), and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z zl zc x xl xc sh : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [z, zl, zc, x, xl, xc, sh] 1 s ∧
    (Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        1 ≤ sh.toNat ∧ sh.toNat ≤ 63 ∧
        (x.toNat ≤ z.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8 ∧ Apart x.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn0 s s' ∧
        (s'.mem.readLE z.toNat (8 * zl.toNat) = (s.mem.readLE x.toNat (8 * zl.toNat) * 2 ^ sh.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 7 1 =
          [BitVec.ofNat 64 ((s.mem.readLE x.toNat (8 * zl.toNat) * 2 ^ sh.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 64, s.sp.toNat + 72)])) :=
  ⟨ret, s0, _, _, _, _, _, _, _, hret, setup, hpre,
    correctness _ _ _ _ _ _ _ ret hret s0 setup hpre⟩

end Witness

end FvModexp.Arm64.LshVU
