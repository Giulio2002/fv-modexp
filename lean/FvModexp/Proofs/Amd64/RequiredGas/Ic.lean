import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.IcLZ
import FvModexp.Proofs.Amd64.RequiredGas.IcLN
import FvModexp.Proofs.Amd64.RequiredGas.IcHZ
import FvModexp.Proofs.Amd64.RequiredGas.IcHN

/-! `modexpIterationCount` (amd64) as a summary for every input: the result register is `Geth.iterationCount` (GethGas.lean); the four
cases (`expLen ≤ 32` or not × lowest limb of the exponent head zero or not, the `BSR`-of-zero path) combined. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

theorem ic_summary : Summary Extracted.program icA IcPre IcPost := by
  intro s hpc hp
  by_cases c1 : (s.regs 0).toNat ≤ 32 <;> by_cases q0 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = 0
  · exact ic_LZ s hpc ⟨hp, c1, q0⟩
  · exact ic_LN s hpc ⟨hp, c1, q0⟩
  · exact ic_HZ s hpc ⟨hp, by omega, q0⟩
  · exact ic_HN s hpc ⟨hp, by omega, q0⟩

end FvModexp.Amd64.RG
