import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Blk2Lt
import FvModexp.Proofs.Arm64.RequiredGas.Blk2Ge

/-! `RequiredGas` (arm64) from `+0xc4` (the first length word parsed) to the return: the second `getData(input, 32, 32)` +
`SetBytes`, then `rg_blk3`. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

theorem rg_blk2 (k : Blk3Stmt) : Blk2Stmt := by
  intro c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_x5 w0 _
  by_cases d0 : len.toNat < cap.toNat
  · exact rg_blk2_Lt k c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_x5 w0 d0
  · exact rg_blk2_Ge k c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_x5 w0 d0

end FvModexp.Arm64.RG
