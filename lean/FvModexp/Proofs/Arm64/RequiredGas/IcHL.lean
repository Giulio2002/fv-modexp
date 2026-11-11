import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.IcDefs

/-! `modexpIterationCount` (arm64) summary, case `32 < (s.regs 0).toNat`, `s.mem.readLE (s.sp.toNat + 32) 8 = 0` (see `IcDefs`). -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem ic_HL : Summary Extracted.program icA (fun s => IcPre s ∧ 32 < (s.regs 0).toNat ∧ s.mem.readLE (s.sp.toNat + 32) 8 = 0) IcPost := by
  intro s hpc ⟨⟨⟨hr1, hr2⟩, h16, hal, hsp, hacc⟩, c1, c2⟩
  janus_run [len64_readLE, c1, c2]
  all_goals first
    | (exfalso; omega)
    | (refine Ret.retX_mem rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun i hi => ?_) rfl
       simp at hi; subst hi
       apply BitVec.eq_of_toNat_eq
       janus_simp
       have L0 := Util.readLE8_lt s.mem (s.sp.toNat + 8); have L1 := Util.readLE8_lt s.mem (s.sp.toNat + 16)
       have L2 := Util.readLE8_lt s.mem (s.sp.toNat + 24); have L3 := Util.readLE8_lt s.mem (s.sp.toNat + 32)
       have c0 := Geth.bitLen_le _ 64 L0; have c1 := Geth.bitLen_le _ 64 L1; have c2 := Geth.bitLen_le _ 64 L2; have c3 := Geth.bitLen_le _ 64 L3
       have z0 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 8) 8)).1; have z1 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 16) 8)).1
       have z2 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 24) 8)).1; have z3 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 32) 8)).1
       have y0 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 8) 8)).2; have y1 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 16) 8)).2
       have y2 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 24) 8)).2; have y3 := (Geth.bitLen_zero_iff (s.mem.readLE (s.sp.toNat + 32) 8)).2
       rw [L4, Geth.iterationCount]
       simp (disch := omega) only [Geth.bitLen_limbs]
       simp only [BitVec.toNat_sub, BitVec.toNat_add, umulh16, BitVec.toNat_mul, BitVec.toNat_ofNat, toInt_le_zero, Geth.maxU64, Nat.reducePow,
         Janus.Arm64.addWithCarry_fst_toNat, Janus.Arm64.addWithCarry_c64, Bool.toNat_false, Bool.toNat_true, Nat.add_zero,
         Nat.zero_mod, Nat.zero_add] at *
       try simp (disch := omega) only [Janus.Arm64.dec_add_div] at *
       first
         | done
         | (generalize s.mem.readLE (s.sp.toNat + 8) 8 = l0 at *; generalize s.mem.readLE (s.sp.toNat + 16) 8 = l1 at *
            generalize s.mem.readLE (s.sp.toNat + 24) 8 = l2 at *; generalize s.mem.readLE (s.sp.toNat + 32) 8 = l3 at *
            generalize Aux.bitLen l0 = b0 at *; generalize Aux.bitLen l1 = b1 at *; generalize Aux.bitLen l2 = b2 at *
            generalize Aux.bitLen l3 = b3 at *
            
            try simp only [Nat.reducePow] at *
            repeat' split
            all_goals first
              | omega
              | ((try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *) <;> omega)))

end FvModexp.Arm64.RG
