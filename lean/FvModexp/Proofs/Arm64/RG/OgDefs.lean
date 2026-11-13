import Extracted
import FvModexp.Proofs.Arm64.RG.IcDefs

/-! The callee contracts of the `RequiredGas` main body (arm64) as named `Prop`s — `SetBytes` (`sb`), `memmove` (`mv`),
`osakaModexpGas` (`og_summary`) — so that the segment modules (Blk*, Fin*) take them as hypotheses and compile in parallel with
the callee proofs (Sb*, Mv, Ic*, Og); `RequiredGas.lean` instantiates them. Also `OgPre`/`L4at` (moved from `Og`). -/

set_option autoImplicit false

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

abbrev OgPre (s : State) : Prop :=
  LR s ∧ GuardOK s 0 ∧ StackOK s 88 40 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 128

/-- The `L4` value of the four limbs at `a`. -/
abbrev L4at (m : Memory) (a : Nat) : Nat := L4 (m.readLE a 8) (m.readLE (a + 8) 8) (m.readLE (a + 16) 8) (m.readLE (a + 24) 8)

/-- The statement of `sb` (`Sb.lean`). -/
abbrev SbSum : Prop := Summary Extracted.program sbA (fun s => SbPre (s.regs 2).toNat s ∧ (s.regs 2).toNat ≤ 32)
    (fun s s' => SbPost (s.regs 2).toNat s s')

/-- The statement of `mv` (`Mv.lean`). -/
abbrev MvSum : Prop := Summary Extracted.program mvA (fun s => MvPre (s.regs 2).toNat s ∧ (s.regs 2).toNat ≤ 32)
    (fun s s' => MvPost (s.regs 2).toNat s s')

/-- The statement of `og_summary` (`Og.lean`). -/
abbrev OgSum : Prop := Summary Extracted.program ogA OgPre
    (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      s' = retStateX s junk [BitVec.ofNat 64 (Geth.osakaModexpGas (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat
          (L4 (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) (s.mem.readLE (s.sp.toNat + 24) 8)
            (s.mem.readLE (s.sp.toNat + 32) 8)))] f v m ex ep ∧ MemFrame s.mem m [(s.sp.toNat - 88, s.sp.toNat - 8)])

end FvModexp.Arm64.RG
