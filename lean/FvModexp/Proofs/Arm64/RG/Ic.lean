import Extracted
import FvModexp.Proofs.Arm64.RG.IcLL
import FvModexp.Proofs.Arm64.RG.IcLN
import FvModexp.Proofs.Arm64.RG.IcHL
import FvModexp.Proofs.Arm64.RG.IcHN

/-! `modexpIterationCount` (arm64) as a summary for every input: the four cases of `IcLL`/`IcLN`/`IcHL`/`IcHN` combined. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

theorem ic_summary : Summary Extracted.program icA IcPre IcPost := by
  intro s hpc hp
  by_cases c1 : (s.regs 0).toNat ≤ 32 <;> by_cases c2 : s.mem.readLE (s.sp.toNat + 32) 8 = 0
  · exact ic_LL s hpc ⟨hp, c1, c2⟩
  · exact ic_LN s hpc ⟨hp, c1, c2⟩
  · exact ic_HL s hpc ⟨hp, by omega, c2⟩
  · exact ic_HN s hpc ⟨hp, by omega, c2⟩

end FvModexp.Arm64.RG
