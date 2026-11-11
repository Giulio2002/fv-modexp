import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Seg

/-! `RequiredGas` (arm64) from `+0x204` (the three length words are parsed into `uint256`s) to the return: `Uint64()`/`IsUint64()`
saturation (contracts.go:612-623), then `rg_fin2`. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- `rg_fin2` with the three lengths read from the state's registers. -/
theorem rg_fin2' (k : Fin2Stmt) (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x260)))
    (hsp : S.sp = s.sp - 416#64)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE (s.sp.toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE (s.sp.toNat + 32) 8 = cap.toNat)
    (hB : (S.regs 0).toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 0))
    (hE : (S.regs 1).toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 32))
    (hM : (S.regs 2).toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 64)) :
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s') :=
  k c ptr len cap _ _ _ ret hret s S hpre hpc hsp rfl rfl rfl h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap hB hE hM trivial

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_fin1 (k : Fin2Stmt) : Fin1Stmt := by
  intro c ptr len cap ret hret s S hpre hpc hsp h0 h4 h18 h28 h29 hf hdl m_ret m_fp m_c m_ptr m_len m_cap m_z0 m_z1 w0 w1 w2
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [Disjoint] at hd1 hd2 hdg
  janus_run [hsp, h0, h4, h18, h28, h29, m_z0, m_z1] until [Extracted.entry + 0x260]
  all_goals
    refine reaches_of_returns (rg_fin2' k c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (show MemFrame _ _ _; janus_frame)
      | (show Extracted.program.DataLoaded _; dl_close)
      | (show BitVec.toNat _ = RgSpec.sat _
         rw [show s.sp.toNat - 192 = s.sp.toNat - 216 + 24 by omega, show s.sp.toNat - 200 = s.sp.toNat - 216 + 16 by omega,
           show s.sp.toNat - 208 = s.sp.toNat - 216 + 8 by omega] <;> skip
         first
           | (rw [← w0]; exact sat_bv _ _)
           | (rw [← w1]; exact sat_bv _ _)
           | (rw [← w2]; exact sat_bv _ _))
      | (dsimp only; simp (disch := omega) only [setReg_apply, Nat.reduceEqDiff, ite_false, ite_true, h18, h28, h29,
           Memory.readLE_writeLE_of_disjoint, m_ret, m_fp, m_c, m_ptr, m_len, m_cap]; done)
      | (show State.regs _ _ = _; simp [setReg, h18, h28, h29])

end FvModexp.Arm64.RG
