import Extracted
import FvModexp.Proofs.Common.Util
import FvModexp.Proofs.Common.GethGas
import FvModexp.Proofs.Amd64.RG.Defs

/-! Definitions and lemmas of the `modexpIterationCount` summary (amd64): the result register is the `Nat` model of
`Proofs/Common/GethGas.lean` (a transcription of the Go source), for every input. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- A 256-bit value from its four 64-bit limbs (the exponent head passed by value on the stack); a name of its own so that the
executor rewrites the limb reads but does not split the sum. -/
def L4 (a b c d : Nat) : Nat := a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d

theorem L4_val256 (m : Memory) (a : Nat) :
    L4 (m.readLE a 8) (m.readLE (a + 8) 8) (m.readLE (a + 16) 8) (m.readLE (a + 24) 8) = val256 m a := by
  rw [val256_limbs]; rfl

/-- `BSR` of a 64-bit word (`63 - CLZ`, also for zero: `0`) is its bit length minus one. -/
theorem bsr_readLE (m : Memory) (a : Nat) :
    63 - Janus.Arm64.clzNat 64 (m.readLE a 8) = Aux.bitLen (m.readLE a 8) - 1 := by
  have h := Util.clz_bl 64 _ (Util.readLE8_lt m a)
  omega

/-- A carry flag materialised by `SBB`/`NEG` (`1` or `0`) is zero iff the carry condition fails. -/
theorem carry_eq0 (c : Prop) [Decidable c] : ((if c then 1#64 else 0#64).toNat = 0) ↔ ¬ c := by
  by_cases h : c <;> simp [h]

theorem bitLen_zero : Aux.bitLen 0 = 0 := by simp [Aux.bitLen]

abbrev icA : Nat := segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.modexpIterationCount"

/-- The precondition of the `modexpIterationCount` summary (`RAX = expLen`, `RBX = 16`, `expHead` at `[RSP + 8, RSP + 40)`). -/
abbrev IcPre (s : State) : Prop :=
  RA s ∧ s.regs 3 = 16#64 ∧ (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat + 8) 32 false = true

/-- The postcondition of the `modexpIterationCount` summary. -/
abbrev IcPost : State → State → Prop :=
  fun s s' => ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [BitVec.ofNat 64 (Geth.iterationCount (s.regs 0).toNat (L4 (s.mem.readLE ((s.regs 4).toNat + 8) 8)
      (s.mem.readLE ((s.regs 4).toNat + 16) 8) (s.mem.readLE ((s.regs 4).toNat + 24) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)) 16)]
      f x yh s.mem zh kr

end FvModexp.Amd64.RG
