import Extracted
import FvModexp.Proofs.Amd64.RG.Blk2Lt
import FvModexp.Proofs.Amd64.RG.Blk2Ge

set_option autoImplicit false

/-! `RequiredGas` (amd64) from `+0xf4` (the first length word parsed) to the return: the second `getData(input, 32, 32)` +
`SetBytes`, then `rg_blk3`. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

theorem rg_blk2 (hsb : SbSum) (hmv : MvSum) (k : Blk3Stmt) : Blk2Stmt := by
  intro c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_x5 w0 _
  by_cases d0 : len.toNat < cap.toNat
  · exact rg_blk2_Lt hsb hmv k c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_x5 w0 d0
  · exact rg_blk2_Ge hsb hmv k c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_x5 w0 d0

end FvModexp.Amd64.RG
