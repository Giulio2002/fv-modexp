import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Blk2
import FvModexp.Proofs.Amd64.RequiredGas.Blk3
import FvModexp.Proofs.Amd64.RequiredGas.Fin1
import FvModexp.Proofs.Amd64.RequiredGas.Fin

/-!
# `(*bigModExp).RequiredGas(input []byte) uint64` (amd64), go-ethereum v1.17.10 core/vm/contracts.go:606-646

**Guarantee** (`correctness`). For the Osaka receiver (`eip2565`, `eip7823`, `eip7883` all true, `RAX`) and every input slice
(`RBX`, `RCX`, `RDI`), the call returns (no fault, no panic) with the Go ABI preserved, and for every fork from Fusaka on, when the
three length headers pass EIP-7823 (`Spec.LengthsPass`), the `uint64` result (`RAX`) is EthLib's `requiredGas fork data
(parseLengths data)` with `data` the input bytes.
-/

namespace FvModexp.Amd64.RequiredGas

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp.Amd64.RG

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem run (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap] (RgPre c ptr len cap) (fun s s' => RgPost ptr len s s') := by
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hx15, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  simp only [Janus.Spec.Disjoint] at hd1 hd2 hdg
  janus64_data hd [hacc]
  by_cases c32 : len.toNat < 32
  all_goals janus64_run [c32, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt]
    until [Extracted.entry + 0xf4] calls [sb, mv]
  all_goals
    refine reaches_of_returns (rg_blk2 (rg_blk3 (rg_fin1 rg_fin2)) c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial)
      (fun s' h => h)
    · with_reducible rfl
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
    · dsimp only; simp only [ite_true]; rfl
    · janus_frame
    · dl_close
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
    · dsimp only; simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ite_true, ite_false, or_false, false_or, or_true, or_self, getD_cons_zero]
    · janus64_simp; split <;> omega
    · dsimp only
      refine Eq.trans (by with_reducible assumption) ?_
      refine fromBE_eq_of (by omega) (fun i hi => ?_)
      set_option maxHeartbeats 2000000 in
      unfold Calldata.pad
      split
      · first
          | (refine (copy_rd (by with_reducible assumption) (by omega)).trans ?_
             simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
             exact rd_self (by omega))
          | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
             exact rd_self (by omega))
      · first
          | (exfalso; omega)
          | (refine (rd_out (by with_reducible assumption) (by omega)).trans ?_
             rcases (show i < 16 ∨ (16 ≤ i ∧ i < 32) by omega) with hq | hq <;>
               simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
                 Nat.zero_div, Nat.zero_mod])


/-- **Row 2 (amd64).** `(*bigModExp).RequiredGas` with the Osaka receiver: returns for every input, and when the lengths pass EIP-7823
the result is EthLib's `requiredGas` at every fork from Fusaka on. -/
theorem correctness (c ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, ptr, len, cap]
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ StackGuardOK s 456 ∧ StackWritable s 496 40 ∧ Extracted.program.DataLoaded s.mem ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ Buffer s ptr len.toNat false ∧ Buffer s c 3 false ∧
        Spec.OsakaReceiver s.mem c.toNat ∧ Janus.Spec.Disjoint ptr.toNat len.toNat ((s.regs 4).toNat - 496) 536 ∧
        Janus.Spec.Disjoint c.toNat 3 ((s.regs 4).toNat - 496) 536 ∧ Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 496) 536)
      (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) := by
  intro ret hret s hs ⟨h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have h2 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := by
    have hr := hs.ret; simp only [regSP, Janus.Amd64.Program.withExit] at hr; rw [hr]; exact hret.user
  exact run c ptr len cap ret hret s hs ⟨⟨h1, h2, h3⟩, h4, h5, hs.zero, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

namespace Witness

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
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry
    [BitVec.ofNat 64 cA, BitVec.ofNat 64 inA, 96, 96] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ StackGuardOK s 456 ∧ StackWritable s 496 40 ∧ Extracted.program.DataLoaded s.mem ∧
        (96 : BitVec 64).toNat ≤ (96 : BitVec 64).toNat ∧ (96 : BitVec 64).toNat < 2 ^ 48 ∧ Buffer s (BitVec.ofNat 64 inA) (96 : BitVec 64).toNat false ∧ Buffer s (BitVec.ofNat 64 cA) 3 false ∧
        Spec.OsakaReceiver s.mem (BitVec.ofNat 64 cA).toNat ∧ Janus.Spec.Disjoint (BitVec.ofNat 64 inA).toNat (96 : BitVec 64).toNat ((s.regs 4).toNat - 496) 536 ∧
        Janus.Spec.Disjoint (BitVec.ofNat 64 cA).toNat 3 ((s.regs 4).toNat - 496) 536 ∧ Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 496) 536) s0 := by
  refine ⟨by decide, by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    by unfold Janus.Amd64.Program.DataLoaded; decide, by decide, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_⟩ <;> (unfold Janus.Spec.Disjoint; decide)

/-- **Non-vacuity**: a concrete Osaka-receiver call with 96 zero bytes satisfies the precondition (and returns). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (c ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [c, ptr, len, cap] s ∧
    (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ StackGuardOK s 456 ∧ StackWritable s 496 40 ∧ Extracted.program.DataLoaded s.mem ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ Buffer s ptr len.toNat false ∧ Buffer s c 3 false ∧
        Spec.OsakaReceiver s.mem c.toNat ∧ Janus.Spec.Disjoint ptr.toNat len.toNat ((s.regs 4).toNat - 496) 536 ∧
        Janus.Spec.Disjoint c.toNat 3 ((s.regs 4).toNat - 496) 536 ∧ Janus.Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 496) 536) s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (fun s s' => ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
        Spec.u64 (s'.regs 0) = EthLib.Execution.Evm.Precompiles.Modexp.requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
          (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))) s s' :=
  ⟨ret, s0, _, _, _, _, hret, setup, hpre, correctness _ _ _ _ ret hret s0 setup hpre⟩

end Witness

end FvModexp.Amd64.RequiredGas
