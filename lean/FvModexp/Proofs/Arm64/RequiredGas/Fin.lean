import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.FinA
import FvModexp.Proofs.Arm64.RequiredGas.FinB
import FvModexp.Proofs.Arm64.RequiredGas.FinC
import FvModexp.Proofs.Arm64.RequiredGas.FinD
import FvModexp.Proofs.Arm64.RequiredGas.FinE

/-! `RequiredGas` (arm64) from `+0x260` (the three lengths are in `X0`-`X2`, saturated to `uint64`) to the return: the four cases of
the exponent-head slice bounds combined. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

theorem rg_fin2 : Fin2Stmt := by
  intro c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM _
  by_cases k2 : finK2 cap B
  · by_cases k1 : finK1 len B E <;> by_cases k3 : finK3 len B
    · exact rg_fin2_A c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM ⟨k2, k1, k3⟩
    · exact rg_fin2_B c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM ⟨k2, k1, k3⟩
    · exact rg_fin2_C c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM ⟨k2, k1, k3⟩
    · exact rg_fin2_D c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM ⟨k2, k1, k3⟩
  · exact rg_fin2_E c ptr len cap B E M ret hret s S hpre hpc hsp h0 h1 h2 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM k2

end FvModexp.Arm64.RG
