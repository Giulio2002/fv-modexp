import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Seg

/-! `RequiredGas` (amd64) from `+0x2c2` (the three length words are parsed into `uint256`s) to the return: `Uint64()`/`IsUint64()`
saturation (contracts.go:612-623), then `rg_fin2`. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- `rg_fin2` with the three lengths read from the state's registers. -/
theorem rg_fin2' (k : Fin2Stmt) (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.rip = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x324)))
    (h4 : S.regs 4 = s.regs 4 - 400#64) (h14 : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - 496, (s.regs 4).toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.regs 4).toNat 8 = ret) (m_fp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m_c : S.mem.readLE ((s.regs 4).toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE ((s.regs 4).toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE ((s.regs 4).toNat + 32) 8 = cap.toNat)
    (hB : (S.regs 0).toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 0))
    (hE : (S.regs 3).toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 32))
    (hM : (S.regs 1).toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 64)) :
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s') :=
  k c ptr len cap _ _ _ ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap rfl rfl rfl hB hE hM trivial

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_fin1 (k : Fin2Stmt) : Fin1Stmt := by
  intro c ptr len cap ret hret s S hpre hpc h4 h14 hx hf hdl m_ret m_fp m_c m_ptr m_len m_cap h0 h2 m_z0 m_z1 w0 w1 w2
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hx15, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [regSP] at hlow hnw hacc
  simp only [Janus.Spec.Disjoint] at hd1 hd2 hdg
  janus64_run [h4, h14, hx, h0, h2, m_z0, m_z1] until [Extracted.entry + 0x324]
  refine reaches_of_returns (rg_fin2' k c ptr len cap ret hret s _ hpre' ?hpc ?h4 ?h14 ?hx ?hf ?hdl ?m_ret ?m_fp ?m_c ?m_ptr
    ?m_len ?m_cap ?hB ?hE ?hM) (fun s' h => h)
  case hpc => with_reducible rfl
  case h4 => exact h4
  case h14 => exact h14
  case hx => exact hx
  case hf => exact hf
  case hdl => exact hdl
  case m_ret => exact m_ret
  case m_fp => exact m_fp
  case m_c => exact m_c
  case m_ptr => exact m_ptr
  case m_len => exact m_len
  case m_cap => exact m_cap
  all_goals
    dsimp only; simp only [setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false]
    try rw [show (s.regs 4).toNat - 192 = (s.regs 4).toNat - 216 + 24 by omega,
      show (s.regs 4).toNat - 200 = (s.regs 4).toNat - 216 + 16 by omega,
      show (s.regs 4).toNat - 208 = (s.regs 4).toNat - 216 + 8 by omega]
  case hB => rw [← w0]; exact sat_bv _ _
  case hE => rw [← w1]; exact sat_bv _ _
  case hM => rw [← w2]; exact sat_bv _ _

end FvModexp.Amd64.RG
