-- LEGACY (retired from the release, coordinator 2026-11-15): standalone row on the single-function extraction of `AddMulVVWW`; its Run-extraction coverage is `Proofs/Amd64/AddMulVVWWSum.lean` via the rows in docs/COVERAGE.md "Legacy standalone rows". Run on demand: scripts/asm-row.sh.
import Extracted
import FvModexp.Proofs.Amd64.AddMulVVWWSum

/-!
# Row: `math/big.addMulVVWW.abi0` (go-bigmodexpfix arith_amd64.s, Go assembly, ABI0, amd64; both code paths)

**Guarantee** (`correctness`). For every ABI0 call of `addMulVVWW(z, x, y []Word, m, a Word) (c Word)` with
`n = len(z)`, `z[0:n]` writable, `x[0:n]`, `y[0:n]` readable, `z` equal to or disjoint from each of `x`, `y`, `z[0:n]`
disjoint from the call frame, and the byte `math/big.hasADX` readable — **whatever its value**, so both the `MULQ` path
and the `MULXQ`/`ADCXQ`/`ADOXQ` path are covered: the call returns (no fault, every length), pops the return address,
keeps `RBP`, the `FS` base and `DF`, and the `n` limbs at `z` hold `(X + Y·m + a) mod 2^(64 n)`, the result word is
`(X + Y·m + a) / 2^(64 n)` (`X`, `Y` the little-endian values of `x[0:n]`, `y[0:n]` before the call); nothing else
changes but `z[0:n]` and the result word. Two witnesses: `nonvacuous` (`hasADX = 0`) and `nonvacuous_adx`
(`hasADX = 1`). The library summary `AddMulVVWWSum.addMulVVWW_summary` specialised to this extraction.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec

namespace FvModexp.Amd64.AddMulVVWW

theorem correctness (z zl zc x xl xc y yl yc m a : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc, m, a] 1
      (fun s => s.mem.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
        Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 104)
      (fun s s' =>
        s'.mem.readLE z.toNat (8 * zl.toNat) =
          (s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) %
            2 ^ (64 * zl.toNat) ∧
        results0 s s' 11 1 = [BitVec.ofNat 64
          ((s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) /
            2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]) :=
  FvModexp.Amd64.AddMulVVWWSum.ensures z zl zc x xl xc y yl yc m a

/-- the same contract on the ADX path (`hasADX ≠ 0`): stated separately only so that the witness
`Witness.correctness_adx` shows this path's hypotheses satisfiable -/
theorem correctness_adx (z zl zc x xl xc y yl yc m a : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc, m, a] 1
      (fun s => s.mem.readLE Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 = 1 ∧
        s.mem.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
        Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 104)
      (fun s s' =>
        s'.mem.readLE z.toNat (8 * zl.toNat) =
          (s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) %
            2 ^ (64 * zl.toNat) ∧
        results0 s s' 11 1 = [BitVec.ofNat 64
          ((s.mem.readLE x.toNat (8 * zl.toNat) + s.mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) /
            2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]) := by
  janus64_ensures_old [Janus.Spec.Ptr]
  exact (fun ret hret s hs ⟨_, hp⟩ => (correctness z zl zc x xl xc y yl yc m a).toOld ret hret s hs hp)


namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def dat : Nat := 0x300000
def adx : Nat := 0xbb6b8a

/-- the 64-bit words of the witness memory (little-endian), all other bytes `0`; the flag byte `hasADX = 0` -/
def words : List (Nat × Nat) :=
  [(sp0, ret), (sp0 + 8, dat), (sp0 + 16, 1), (sp0 + 24, 1), (sp0 + 32, dat), (sp0 + 40, 1), (sp0 + 48, 1),
   (sp0 + 56, dat + 0x40), (sp0 + 64, 1), (sp0 + 72, 1), (sp0 + 80, 2 ^ 64 - 1), (sp0 + 88, 5),
   (dat, 3), (dat + 0x40, 2 ^ 64 - 1), (adx, 0)]

def bytes (a : Nat) : Byte :=
  match words.find? (fun w => w.1 ≤ a && a < w.1 + 8) with
  | some (b, v) => BitVec.ofNat 8 (v / 2 ^ (8 * (a - b)))
  | none => 0

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨dat, 0x100, true⟩, ⟨adx, 8, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 dat
def y : BitVec 64 := BitVec.ofNat 64 (dat + 0x40)
def m : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 1)

theorem setup : CallSetupF Extracted.entry [z, 1, 1, z, 1, 1, y, 1, 1, m, 5] 1 s0 :=
  ⟨rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide,
   ⟨by decide, by decide⟩, rfl⟩

theorem hpre : s0.mem.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
    Ptr s0.mem z (8 * (1 : BitVec 64).toNat) true ∧ Ptr s0.mem z (8 * (1 : BitVec 64).toNat) false ∧
    Ptr s0.mem y (8 * (1 : BitVec 64).toNat) false ∧
    (z.toNat = z.toNat ∨ Apart z.toNat (8 * (1 : BitVec 64).toNat) z.toNat (8 * (1 : BitVec 64).toNat)) ∧
    (z.toNat = y.toNat ∨ Apart z.toNat (8 * (1 : BitVec 64).toNat) y.toNat (8 * (1 : BitVec 64).toNat)) ∧
    Apart z.toNat (8 * (1 : BitVec 64).toNat) (s0.regs 4).toNat 104 := by
  simp only [Ptr, Apart]; decide

/-- All the hypotheses of `correctness` hold together at a concrete call (the MULQ path; `n = 1`, in place `z = x = [3]`,
`y = [2^64 - 1]`, `m = 2^64 - 1`, `a = 5`), and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z zl zc x xl xc y yl yc m a : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetupF Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc, m, a] 1 s ∧
    s.mem.readLE Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 = 0 ∧
    (s.mem.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
        Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 104) ∧
    Returns (Extracted.program.withExit ret) (s.setRet ret) (fun s' => ABIReturn0 (s.setRet ret) s' ∧ (s'.mem.readLE z.toNat (8 * zl.toNat) =
          ((s.setRet ret).mem.readLE x.toNat (8 * zl.toNat) + (s.setRet ret).mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) %
            2 ^ (64 * zl.toNat) ∧
        results0 (s.setRet ret) s' 11 1 = [BitVec.ofNat 64
          (((s.setRet ret).mem.readLE x.toNat (8 * zl.toNat) + (s.setRet ret).mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) /
            2 ^ (64 * zl.toNat))] ∧
        MemFrame (s.setRet ret).mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (((s.setRet ret).regs 4).toNat + 96, ((s.setRet ret).regs 4).toNat + 104)])) :=
  ⟨ret, s0, z, 1, 1, z, 1, 1, y, 1, 1, m, 5, hret, setup, by decide, hpre,
    (correctness z 1 1 z 1 1 y 1 1 m 5) s0 setup hpre ret hret⟩

end Witness

namespace Witness.Adx

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def dat : Nat := 0x300000
def adx : Nat := 0xbb6b8a

/-- the 64-bit words of the witness memory (little-endian), all other bytes `0`; the flag byte `hasADX = 1` -/
def words : List (Nat × Nat) :=
  [(sp0, ret), (sp0 + 8, dat), (sp0 + 16, 1), (sp0 + 24, 1), (sp0 + 32, dat), (sp0 + 40, 1), (sp0 + 48, 1),
   (sp0 + 56, dat + 0x40), (sp0 + 64, 1), (sp0 + 72, 1), (sp0 + 80, 2 ^ 64 - 1), (sp0 + 88, 5),
   (dat, 3), (dat + 0x40, 2 ^ 64 - 1), (adx, 1)]

def bytes (a : Nat) : Byte :=
  match words.find? (fun w => w.1 ≤ a && a < w.1 + 8) with
  | some (b, v) => BitVec.ofNat 8 (v / 2 ^ (8 * (a - b)))
  | none => 0

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨dat, 0x100, true⟩, ⟨adx, 8, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 dat
def y : BitVec 64 := BitVec.ofNat 64 (dat + 0x40)
def m : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 1)

theorem setup : CallSetupF Extracted.entry [z, 1, 1, z, 1, 1, y, 1, 1, m, 5] 1 s0 :=
  ⟨rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide,
   ⟨by decide, by decide⟩, rfl⟩

theorem hpre : s0.mem.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
    Ptr s0.mem z (8 * (1 : BitVec 64).toNat) true ∧ Ptr s0.mem z (8 * (1 : BitVec 64).toNat) false ∧
    Ptr s0.mem y (8 * (1 : BitVec 64).toNat) false ∧
    (z.toNat = z.toNat ∨ Apart z.toNat (8 * (1 : BitVec 64).toNat) z.toNat (8 * (1 : BitVec 64).toNat)) ∧
    (z.toNat = y.toNat ∨ Apart z.toNat (8 * (1 : BitVec 64).toNat) y.toNat (8 * (1 : BitVec 64).toNat)) ∧
    Apart z.toNat (8 * (1 : BitVec 64).toNat) (s0.regs 4).toNat 104 := by
  simp only [Ptr, Apart]; decide

/-- All the hypotheses of `correctness` hold together at a concrete call (the ADX path; `n = 1`, in place `z = x = [3]`,
`y = [2^64 - 1]`, `m = 2^64 - 1`, `a = 5`), and it returns. -/
theorem _root_.FvModexp.Amd64.AddMulVVWW.Witness.correctness_adx : ∃ (ret : Nat) (s : State) (z zl zc x xl xc y yl yc m a : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetupF Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc, m, a] 1 s ∧
    (s.mem.readLE Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 = 1 ∧
    s.mem.accessible Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.hasADX» 1 false = true ∧
        Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 104) ∧
    Returns (Extracted.program.withExit ret) (s.setRet ret) (fun s' => ABIReturn0 (s.setRet ret) s' ∧ (s'.mem.readLE z.toNat (8 * zl.toNat) =
          ((s.setRet ret).mem.readLE x.toNat (8 * zl.toNat) + (s.setRet ret).mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) %
            2 ^ (64 * zl.toNat) ∧
        results0 (s.setRet ret) s' 11 1 = [BitVec.ofNat 64
          (((s.setRet ret).mem.readLE x.toNat (8 * zl.toNat) + (s.setRet ret).mem.readLE y.toNat (8 * zl.toNat) * m.toNat + a.toNat) /
            2 ^ (64 * zl.toNat))] ∧
        MemFrame (s.setRet ret).mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (((s.setRet ret).regs 4).toNat + 96, ((s.setRet ret).regs 4).toNat + 104)])) :=
  ⟨ret, s0, z, 1, 1, z, 1, 1, y, 1, 1, m, 5, hret, setup, ⟨by decide, hpre⟩,
    (FvModexp.Amd64.AddMulVVWW.correctness_adx z 1 1 z 1 1 y 1 1 m 5) s0 setup ⟨by decide, hpre⟩ ret hret⟩

end Witness.Adx

end FvModexp.Amd64.AddMulVVWW
