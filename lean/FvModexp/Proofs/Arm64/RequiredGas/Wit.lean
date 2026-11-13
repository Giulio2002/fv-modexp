import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Pre

/-! The concrete witness state of `FvModexp.Arm64.RequiredGas.Witness.nonvacuous` (arm64) and its precondition facts (a module of
its own, compiled in parallel with the proof segments). -/

set_option autoImplicit false

namespace FvModexp.Arm64.RG.Wit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def cA : Nat := 0x300000
def inA : Nat := 0x300100
def dat : DataSegment := Extracted.data.head!
def dbase : Nat := janus_eval% dat.base
def dlen : Nat := janus_eval% dat.bytes.length

/-- The jump table of `SetBytes` (read-only data), the Osaka receiver `{true, true, true}` at `cA`, and a 96-byte all-zero input at
`inA` (three zero lengths): every other byte is zero. -/
def bytes (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0)
  else if cA ≤ a ∧ a < cA + 3 then 1 else 0

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 cA else if i = 1 then BitVec.ofNat 64 inA else if i = 2 then 96
      else if i = 3 then 96 else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 504, 544, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩, ⟨cA, 0x200, false⟩]⟩ }

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry
    [BitVec.ofNat 64 cA, BitVec.ofNat 64 inA, 96, 96] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : RgPre (BitVec.ofNat 64 cA) (BitVec.ofNat 64 inA) 96 96 s0 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by unfold Program.DataLoaded; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_⟩ <;> (unfold Disjoint; decide)

end FvModexp.Arm64.RG.Wit
