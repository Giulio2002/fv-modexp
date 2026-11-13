import Extracted
import FvModexp.Proofs.Amd64.RG.IcDefs

/-! The callee contracts of the `RequiredGas` main body (amd64) as named `Prop`s — `SetBytes` (`sb`), `memmove` (`mv`),
`osakaModexpGas` (`og_summary`) — so that the segment modules (Head, Blk*, Fin*) take them as hypotheses and compile in parallel
with the callee proofs (Sb*, Mv, Ic*, Og); `RequiredGas.lean` instantiates them. Also `ogA`/`OgPre`/`ogHead`/`OgPost` and the
16-byte read lemmas (moved from `Og`). -/

set_option autoImplicit false

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

abbrev ogA : Nat := segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.osakaModexpGas"

/-- The stack `osakaModexpGas` needs: its frame (`PUSH RBP; SUB $0x38`) and the return slot of the `modexpIterationCount` call below
`RSP`, the return address and the 32-byte head above it. -/
abbrev OgPre (s : State) : Prop :=
  RA s ∧ StackGuardOK s 0 ∧ StackWritable s 72 40 ∧
    ((s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16)

/-- The exponent head the caller passed (the four limbs at `RSP + 8`). -/
abbrev ogHead (s : State) : Nat :=
  L4 (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) (s.mem.readLE ((s.regs 4).toNat + 24) 8)
    (s.mem.readLE ((s.regs 4).toNat + 32) 8)

abbrev OgPost (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [BitVec.ofNat 64 (Geth.osakaModexpGas (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (ogHead s))]
      f x yh m zh kr ∧ MemFrame s.mem m [((s.regs 4).toNat - 72, (s.regs 4).toNat)]

theorem rd16_lo (m : Memory) (a : Nat) : m.readLE a 16 / 1 % 18446744073709551616 = m.readLE a 8 := by
  rw [Nat.div_one, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  have := Janus.Arm64.Memory.readLE_lt m a 8
  simp only [Nat.reducePow] at this ⊢
  omega

theorem rd16_hi (m : Memory) (a : Nat) : m.readLE a 16 / 18446744073709551616 = m.readLE (a + 8) 8 := by
  rw [show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  have := Janus.Arm64.Memory.readLE_lt m a 8
  simp only [Nat.reducePow] at this ⊢
  omega

/-- The statement of `sb` (`Sb.lean`). -/
abbrev SbSum : Prop := Summary Extracted.program sbA (fun s => SbPre (s.regs 1).toNat s ∧ (s.regs 1).toNat ≤ 32)
    (fun s s' => SbPost (s.regs 1).toNat s s')

/-- The statement of `mv` (`Mv.lean`). -/
abbrev MvSum : Prop := Summary Extracted.program mvA (fun s => MvPre (s.regs 1).toNat s ∧ (s.regs 1).toNat ≤ 32)
    (fun s s' => MvPost (s.regs 1).toNat s s')

/-- The statement of `og_summary` (`Og.lean`). -/
abbrev OgSum : Prop := Summary Extracted.program ogA OgPre OgPost

end FvModexp.Amd64.RG
