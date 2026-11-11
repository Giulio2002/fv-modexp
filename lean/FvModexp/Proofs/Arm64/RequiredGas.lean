import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Blk2

/-!
# `(*bigModExp).RequiredGas(input []byte) uint64` (arm64), go-ethereum v1.17.10 core/vm/contracts.go:606-646

**Guarantee** (`correctness`). For the Osaka receiver (`eip2565`, `eip7823`, `eip7883` all true) and every input slice, the call
returns (no fault, no panic) with the Go ABI preserved, and for every fork from Fusaka on, when the three length headers pass EIP-7823
(`Spec.LengthsPass`), the `uint64` result is EthLib's `requiredGas fork data (parseLengths data)` with `data` the input bytes.
-/

namespace FvModexp.Arm64.RequiredGas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp.Arm64.RG

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem run (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') := by
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases d0 : len.toNat < cap.toNat
  all_goals janus_run [c32, d0, BitArith.and_asr63, BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt]
    until [Extracted.entry + 0xc4] calls [sb, mv]
  all_goals
    refine reaches_of_returns (rg_blk2 c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (with_reducible show MemFrame _ _ _; janus_frame)
      | (with_reducible show Extracted.program.DataLoaded _; dl_close)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 0
         rw [val256_limbs]; dsimp only; simp only [Nat.reducePow]
         refine Eq.trans (by assumption) ?_
         refine fromBE_eq_of (by omega) (fun i hi => ?_)
         rg_byte)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply]; decide)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply,
           Nat.reduceEqDiff, ite_true, ite_false, or_self, or_false, false_or, getD_cons_zero]
         first
           | done
           | rfl
           | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
      | (with_reducible show Memory.readLE _ _ _ = _; janus_simp; try (split <;> omega))

/-- **Row 2 (arm64).** `(*bigModExp).RequiredGas` with the Osaka receiver: returns for every input, and when the lengths pass EIP-7823
the result is EthLib's `requiredGas` at every fork from Fusaka on. -/
theorem correctness (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap]
      (fun s => GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544)
      (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) :=
  run c ptr len cap

namespace Witness

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

/-- **Non-vacuity**: a concrete Osaka-receiver call with 96 zero bytes satisfies the precondition (and returns). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (c ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [c, ptr, len, cap] s ∧
    (fun s => GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544) s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) s s' :=
  ⟨ret, s0, _, _, _, _, hret, setup, hpre, correctness _ _ _ _ ret hret s0 setup hpre⟩

end Witness

end FvModexp.Arm64.RequiredGas
