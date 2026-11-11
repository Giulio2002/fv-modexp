import Extracted
import FvModexp.Proofs.Common.Ret
import FvModexp.Proofs.Common.GethGas
import FvModexp.Proofs.Arm64.RequiredGas.Defs

/-! `modexpIterationCount` and `osakaModexpGas` (arm64) as summaries: the result register is the `Nat` model of `Proofs/Common/GethGas.lean`
(a transcription of the Go source), for every input. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- A 256-bit value from its four 64-bit limbs (the exponent head passed by value on the stack); a name of its own so that the
executor rewrites the limb reads but does not split the sum. -/
def L4 (a b c d : Nat) : Nat := a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d

theorem L4_val256 (m : Memory) (a : Nat) :
    L4 (m.readLE a 8) (m.readLE (a + 8) 8) (m.readLE (a + 16) 8) (m.readLE (a + 24) 8) = val256 m a := by
  rw [val256_limbs]; rfl

theorem lsr3 (x : BitVec 64) : (x.rotateRight 3 &&& 18446744073709551615#64 &&& 2305843009213693951#64).toNat = x.toNat / 8 := by
  simp only [BitVec.toNat_and, BitVec.toNat_rotateRight, BitVec.toNat_ofNat]
  rw [show (18446744073709551615 : Nat) % 2 ^ 64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2305843009213693951 : Nat) % 2 ^ 64 = 2 ^ 61 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at *
  have e : x.toNat * 2305843009213693952 % 18446744073709551616 = (x.toNat % 8) * 2 ^ 61 := by omega
  rw [e, FvModexp.Util.or_hi _ _ 61 (by omega)]
  omega

theorem rot3_mask (x : BitVec 64) :
    x.rotateRight 3 &&& 18446744073709551615#64 &&& 2305843009213693951#64 = x >>> 3 := by
  apply BitVec.eq_of_toNat_eq
  rw [lsr3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lsr3' (x : BitVec 64) : (x.rotateRight 3).toNat % 2305843009213693952 = x.toNat / 8 := by
  have := lsr3 x
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at this
  rw [show (18446744073709551615 : Nat) % 2 ^ 64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2305843009213693951 : Nat) % 2 ^ 64 = 2 ^ 61 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
  have h2 := (x.rotateRight 3).isLt
  rw [Nat.mod_eq_of_lt h2] at this
  simpa using this

theorem umulh2 (x : BitVec 64) :
    (BitVec.extractLsb' 64 64 (2#128 * BitVec.setWidth 128 x)).toNat = 2 * x.toNat / 18446744073709551616 := by
  have := umulh_toNat 2#64 x
  simpa using this

abbrev icA : Nat := segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.modexpIterationCount"
abbrev ogA : Nat := segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.osakaModexpGas"



/-- `64 - CLZ(x)` (arm64 `bits.Len64`) is the bit length of a 64-bit word. -/
theorem len64_readLE (m : Memory) (a : Nat) :
    64#64 - BitVec.ofNat 64 (clzNat 64 (m.readLE a 8)) = BitVec.ofNat 64 (Aux.bitLen (m.readLE a 8)) := by
  have h := Util.clz_bl 64 _ (Util.readLE8_lt m a)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `umulh x, 16` with the constant folded by the executor. -/
theorem umulh16 (x : BitVec 64) :
    (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 x * 16#128)).toNat = x.toNat * 16 / 18446744073709551616 := by
  have := umulh_toNat x 16#64
  simpa using this

/-- A signed `≤ 0` test (`b.le` after `cmp x, #0`) in unsigned terms. -/
theorem toInt_le_zero (x : BitVec 64) : (x.toInt ≤ 0) ↔ (x.toNat = 0 ∨ 2 ^ 63 ≤ x.toNat) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem ic_summary : Summary Extracted.program icA
    (fun s => LR s ∧ s.regs 1 = 16#64 ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat + 8) 32 false = true)
    (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      s' = retStateX s junk [BitVec.ofNat 64 (Geth.iterationCount (s.regs 0).toNat (L4 (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) (s.mem.readLE (s.sp.toNat + 24) 8)
          (s.mem.readLE (s.sp.toNat + 32) 8)) 16)]
        f v s.mem ex ep) := by
  intro s hpc ⟨⟨hr1, hr2⟩, h16, hal, hsp, hacc⟩
  janus_run [len64_readLE]
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
