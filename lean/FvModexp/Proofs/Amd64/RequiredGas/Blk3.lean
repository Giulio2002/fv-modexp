import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Blk3Lt
import FvModexp.Proofs.Amd64.RequiredGas.Blk3Ge

set_option autoImplicit false

/-! `RequiredGas` (amd64) from `+0x1d0` (two length words parsed) to the return: the third `getData(input, 64, 32)` +
`SetBytes`, then `rg_fin1`. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

theorem rg_blk3 (hsb : SbSum) (hmv : MvSum) (k : Fin1Stmt) : Blk3Stmt := by
  intro c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_z0 w0 w1 _
  by_cases d0 : len.toNat < cap.toNat
  · exact rg_blk3_Lt hsb hmv k c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_z0 w0 w1 d0
  · exact rg_blk3_Ge hsb hmv k c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_z0 w0 w1 d0

end FvModexp.Amd64.RG
