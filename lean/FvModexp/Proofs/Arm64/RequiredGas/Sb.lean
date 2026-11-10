import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.SbA
import FvModexp.Proofs.Arm64.RequiredGas.SbB
import FvModexp.Proofs.Arm64.RequiredGas.SbC

/-! `(*uint256.Int).SetBytes` for every length `≤ 32` (arm64): the 33 per-length summaries combined. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

theorem sb : Summary Extracted.program sbA (fun s => SbPre (s.regs 2).toNat s ∧ (s.regs 2).toNat ≤ 32)
    (fun s s' => SbPost (s.regs 2).toNat s s') := by
  intro s hpc ⟨hpre, hle⟩
  generalize (s.regs 2).toNat = k at *
  have hlt : k < 33 := by omega
  janus_cases hlt
  · exact sb0 s hpc hpre
  · exact sb1 s hpc hpre
  · exact sb2 s hpc hpre
  · exact sb3 s hpc hpre
  · exact sb4 s hpc hpre
  · exact sb5 s hpc hpre
  · exact sb6 s hpc hpre
  · exact sb7 s hpc hpre
  · exact sb8 s hpc hpre
  · exact sb9 s hpc hpre
  · exact sb10 s hpc hpre
  · exact sb11 s hpc hpre
  · exact sb12 s hpc hpre
  · exact sb13 s hpc hpre
  · exact sb14 s hpc hpre
  · exact sb15 s hpc hpre
  · exact sb16 s hpc hpre
  · exact sb17 s hpc hpre
  · exact sb18 s hpc hpre
  · exact sb19 s hpc hpre
  · exact sb20 s hpc hpre
  · exact sb21 s hpc hpre
  · exact sb22 s hpc hpre
  · exact sb23 s hpc hpre
  · exact sb24 s hpc hpre
  · exact sb25 s hpc hpre
  · exact sb26 s hpc hpre
  · exact sb27 s hpc hpre
  · exact sb28 s hpc hpre
  · exact sb29 s hpc hpre
  · exact sb30 s hpc hpre
  · exact sb31 s hpc hpre
  · exact sb32 s hpc hpre

end FvModexp.Arm64.RG
