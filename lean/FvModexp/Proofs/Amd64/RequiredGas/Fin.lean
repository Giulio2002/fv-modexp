import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.FinS
import FvModexp.Proofs.Amd64.RequiredGas.FinA
import FvModexp.Proofs.Amd64.RequiredGas.FinB
import FvModexp.Proofs.Amd64.RequiredGas.FinC
import FvModexp.Proofs.Amd64.RequiredGas.FinD

/-! `RequiredGas` (amd64) from `+0x324` (the three lengths are in `RAX`, `RBX`, `RCX`, saturated to `uint64`) to the return: the
five cases of the exponent-head slice combined. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

theorem rg_fin2 (hsb : SbSum) (hmv : MvSum) (hog : OgSum) : Fin2Stmt := by
  intro c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM _
  by_cases kS : finS len B
  · exact rg_fin2_S hsb hmv hog c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM kS
  · by_cases kE : finE E
    · by_cases kN : finN1 len B
      · exact rg_fin2_A hsb hmv hog c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM ⟨kS, kE, kN⟩
      · exact rg_fin2_B hsb hmv hog c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM ⟨kS, kE, kN⟩
    · by_cases kN : finN2 len B E
      · exact rg_fin2_C hsb hmv hog c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM ⟨kS, kE, kN⟩
      · exact rg_fin2_D hsb hmv hog c ptr len cap B E M ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h3 h1 hB hE hM ⟨kS, kE, kN⟩

end FvModexp.Amd64.RG
