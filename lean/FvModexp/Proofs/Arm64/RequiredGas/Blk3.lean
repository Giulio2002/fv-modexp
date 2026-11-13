import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Blk3Lt
import FvModexp.Proofs.Arm64.RequiredGas.Blk3Ge

/-! `RequiredGas` (arm64) from `+0x160` (two length words parsed) to the return: the third `getData(input, 64, 32)` +
`SetBytes`, then `rg_fin1`. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

theorem rg_blk3 (hsb : SbSum) (hmv : MvSum) (k : Fin1Stmt) : Blk3Stmt := by
  intro c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_z0 w0 w1 _
  by_cases d0 : len.toNat < cap.toNat
  · exact rg_blk3_Lt hsb hmv k c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_z0 w0 w1 d0
  · exact rg_blk3_Ge hsb hmv k c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_z0 w0 w1 d0

end FvModexp.Arm64.RG
