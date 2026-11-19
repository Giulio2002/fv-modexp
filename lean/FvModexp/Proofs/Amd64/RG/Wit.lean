import Extracted
import FvModexp.Proofs.Amd64.RG.Pre

/-! The concrete witness state of `FvModexp.Amd64.RequiredGas.Witness.nonvacuous` (amd64) and its precondition facts (a module of
its own, compiled in parallel with the proof segments). -/

set_option autoImplicit false

namespace FvModexp.Amd64.RG.Wit

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def cA : Nat := 0x300000
def inA : Nat := 0x300100
def dat : DataSegment := Extracted.data.head!
def dbase : Nat := janus_eval% dat.base
def dlen : Nat := janus_eval% dat.bytes.length

/-- The jump table of `SetBytes` (read-only data), the return address at `sp0`, the Osaka receiver `{true, true, true}` at `cA`,
and a 96-byte all-zero input at `inA` (three zero lengths): every other byte is zero. -/
def bytes (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0)
  else if cA ≤ a ∧ a < cA + 3 then 1
  else if sp0 ≤ a ∧ a < sp0 + 8 then BitVec.ofNat 8 (ret / 2 ^ (8 * (a - sp0)))
  else 0

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 cA else if i = 3 then BitVec.ofNat 64 inA else if i = 1 then 96
      else if i = 7 then 96 else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 496, 536, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩, ⟨cA, 0x200, false⟩]⟩ }

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

set_option maxRecDepth 100000 in
theorem setup : CallSetup0 Extracted.entry
    [BitVec.ofNat 64 cA, BitVec.ofNat 64 inA, 96, 96] s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ StackGuardOK s 456 ∧ StackWritable s 496 40 ∧ Extracted.program.DataLoaded s.mem ∧
        (96 : BitVec 64).toNat ≤ (96 : BitVec 64).toNat ∧ (96 : BitVec 64).toNat < 2 ^ 48 ∧ Buffer s (BitVec.ofNat 64 inA) (96 : BitVec 64).toNat false ∧ Buffer s (BitVec.ofNat 64 cA) 3 false ∧
        Spec.OsakaReceiver s.mem (BitVec.ofNat 64 cA).toNat ∧ Janus.Spec.Disjoint (BitVec.ofNat 64 inA).toNat (96 : BitVec 64).toNat ((s.regs 4).toNat - 496) 536 ∧
        Janus.Spec.Disjoint (BitVec.ofNat 64 cA).toNat 3 ((s.regs 4).toNat - 496) 536 ∧ Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 496) 536) s0 := by
  refine ⟨by decide, by decide, (by first | exact ⟨by decide, by decide, by decide, by decide⟩ | exact ⟨by decide, by decide, by decide⟩), (by first | exact ⟨by decide, by decide, by decide, by decide⟩ | exact ⟨by decide, by decide, by decide⟩),
    by unfold Janus.Amd64.Program.DataLoaded; decide, by decide, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    (by first | exact ⟨by decide, by decide, by decide, by decide⟩ | exact ⟨by decide, by decide, by decide⟩), ?_, ?_, ?_⟩ <;> (unfold Janus.Spec.Disjoint; decide)

end FvModexp.Amd64.RG.Wit
