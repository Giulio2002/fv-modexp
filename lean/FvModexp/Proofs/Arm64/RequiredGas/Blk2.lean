import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Blk3

/-! `RequiredGas` (arm64) from `+0xc4` (the first length word parsed) to the return: the second `getData(input, 32, 32)` +
`SetBytes`, then `rg_blk3`. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem rg_blk2 (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0xc4)))
    (hsp : S.sp = s.sp - 416#64) (h0 : S.regs 0 = s.sp - 88#64) (h4 : S.regs 4 = s.sp - 152#64) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE (s.sp.toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE (s.sp.toNat + 32) 8 = cap.toNat)
    (m_x5 : S.mem.readLE (s.sp.toNat - 288) 8 = if len.toNat < 32 then len.toNat else 32)
    (w0 : val256 S.mem (s.sp.toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0) :
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [Disjoint] at hd1 hd2 hdg
  by_cases c32 : len.toNat < 32 <;> by_cases c64 : len.toNat < 64 <;> by_cases d32 : 32 < cap.toNat <;>
    by_cases d0 : len.toNat < cap.toNat
  all_goals try (exfalso; omega)
  all_goals janus_run [hsp, h0, h4, h18, h28, h29, m_ptr, m_len, m_cap, m_x5, c32, c64, d32, d0, BitArith.and_asr63,
    BitArith.and_asr63_lit, Nat.lt_add_right_iff_pos, Nat.mod_eq_of_lt] until [Extracted.entry + 0x160] calls [sb, mv]
  all_goals
    refine reaches_of_returns (rg_blk3 c ptr len cap ret hret s _ hpre' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun s' h => h)
    all_goals first
      | with_reducible rfl
      | (with_reducible show MemFrame _ _ _; janus_frame)
      | (with_reducible show Extracted.program.DataLoaded _; dl_close)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 32
         rw [val256_limbs]; dsimp only; simp only [Nat.reducePow]
         refine Eq.trans (by assumption) ?_
         refine fromBE_eq_of (by omega) (fun i hi => ?_)
         rg_byte)
      | (with_reducible show val256 _ _ = Calldata.word _ _ _ 0; rw [← w0]; unfold val256; janus_simp)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply, h18, h28, h29]; decide)
      | (with_reducible show State.regs _ _ = _; dsimp only; simp only [setReg_apply, callRegs_apply, h18, h28, h29,
           Nat.reduceEqDiff, ite_true, ite_false, or_self, or_false, false_or, getD_cons_zero]
         first
           | done
           | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
      | (with_reducible show Memory.readLE _ _ _ = _; janus_simp [m_ret, m_fp, m_c, m_ptr, m_len, m_cap])

end FvModexp.Arm64.RG
