import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.IcDefs

/-! `modexpIterationCount` (amd64) summary, case `(s.regs 0).toNat ≤ 32`, `s.mem.readLE ((s.regs 4).toNat + 8) 8 = 0` (combined in `Ic`). -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem ic_LZ : Summary Extracted.program icA (fun s => IcPre s ∧ (s.regs 0).toNat ≤ 32 ∧ s.mem.readLE ((s.regs 4).toNat + 8) 8 = 0) IcPost := by
  intro s hpc ⟨⟨⟨hra, hra2, hra3⟩, h16, hsp, hacc⟩, c1, q0⟩
  have L0 := Util.readLE8_lt s.mem ((s.regs 4).toNat + 8); have L1 := Util.readLE8_lt s.mem ((s.regs 4).toNat + 16)
  have L2 := Util.readLE8_lt s.mem ((s.regs 4).toNat + 24); have L3 := Util.readLE8_lt s.mem ((s.regs 4).toNat + 32)
  have c0 := Geth.bitLen_le _ 64 L0; have c1 := Geth.bitLen_le _ 64 L1; have c2 := Geth.bitLen_le _ 64 L2; have c3 := Geth.bitLen_le _ 64 L3
  have z0 := (Geth.bitLen_zero_iff (s.mem.readLE ((s.regs 4).toNat + 8) 8)); have z1 := (Geth.bitLen_zero_iff (s.mem.readLE ((s.regs 4).toNat + 16) 8))
  have z2 := (Geth.bitLen_zero_iff (s.mem.readLE ((s.regs 4).toNat + 24) 8)); have z3 := (Geth.bitLen_zero_iff (s.mem.readLE ((s.regs 4).toNat + 32) 8))
  try simp only [Nat.reducePow] at L0 L1 L2 L3
  janus64_run [bsr_readLE, BitVec.msb_eq_decide, decide_eq_true_eq, carry_eq0, c1, q0]
  all_goals first
    | (exfalso; omega)
    | (refine Ret64.ret_mem rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ rfl rfl rfl
       simp only [getD_cons_zero]
       apply BitVec.eq_of_toNat_eq
       janus64_simp
       rw [L4, Geth.iterationCount]
       simp (disch := omega) only [Geth.bitLen_limbs]
       simp only [Geth.maxU64, Nat.max_def, Nat.reducePow, bitLen_zero] at *
       generalize s.mem.readLE ((s.regs 4).toNat + 8) 8 = l0 at *; generalize s.mem.readLE ((s.regs 4).toNat + 16) 8 = l1 at *
       generalize s.mem.readLE ((s.regs 4).toNat + 24) 8 = l2 at *; generalize s.mem.readLE ((s.regs 4).toNat + 32) 8 = l3 at *
       generalize Aux.bitLen l0 = b0 at *; generalize Aux.bitLen l1 = b1 at *; generalize Aux.bitLen l2 = b2 at *
       generalize Aux.bitLen l3 = b3 at *
       repeat' split
       all_goals first
         | omega
         | (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> omega))

end FvModexp.Amd64.RG
