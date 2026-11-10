import Extracted
import FvModexp.Proofs.Common.Ret
import FvModexp.Proofs.Common.Bytes
import FvModexp.Proofs.Arm64.RequiredGas.Defs

/-! `runtime.memmove(dst, src, n)` for `n ≤ 32` (arm64), run from its extracted code: one symbolic run per length. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem mv : Summary Extracted.program mvA (fun s => MvPre (s.regs 2).toNat s ∧ (s.regs 2).toNat ≤ 32)
    (fun s s' => MvPost (s.regs 2).toNat s s') := by
  intro s hpc ⟨⟨⟨hr1, hr2⟩, _hl0, hd48, hs48, hdw, hsr, hdj, hdl⟩, hn⟩
  simp only [Disjoint] at hdj
  generalize hk : (s.regs 2).toNat = k at *
  have hlt : k < 33 := by omega
  have hl' : s.regs 2 = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by simp [hk]; omega)
  janus_cases hlt
  all_goals
    janus_run
    all_goals first
      | (exfalso; omega)
      | (refine Ret.retX_intro rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun i hi => by simp at hi) (by janus_frame) ⟨?_, ?_⟩
         · intro i hi
           dsimp only
           try simp only [Memory.bytes_writeLE]
           repeat' split
           all_goals first
             | (exfalso; omega)
             | ((try simp (disch := decide) only [Bytes.readLE_mod64]); rw [Bytes.byte_readLE_at _ _ _ _ _ (by omega) (by omega)]; congr 1; omega)
         · dl_close)

end FvModexp.Arm64.RG
