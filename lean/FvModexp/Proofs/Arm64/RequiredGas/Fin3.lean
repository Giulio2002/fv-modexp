import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Pre

/-! `RequiredGas` (arm64) from `+0x3e0` (the exponent head is read) to the return. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- From `+0x3e0` (lengths in `X0`-`X2`, the exponent head at `SP + 0x60`) to the return: the Osaka gas function. -/
theorem rg_fin3 (c ptr len cap B E M : BitVec 64) (H : Nat) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x3e0)))
    (hsp : S.sp = s.sp - 416#64) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)])
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat)
    (h0 : S.regs 0 = B) (h1 : S.regs 1 = E) (h2 : S.regs 2 = M)
    (hH : L4 (S.mem.readLE (s.sp.toNat - 320) 8) (S.mem.readLE (s.sp.toNat - 312) 8) (S.mem.readLE (s.sp.toNat - 304) 8)
      (S.mem.readLE (s.sp.toNat - 296) 8) = H) :
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ s'.regs 0 = BitVec.ofNat 64 (Geth.osakaModexpGas B.toNat E.toNat M.toNat H)) := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hp, hp'⟩, ⟨hcr, hcr'⟩, ⟨ho0, ho1, ho2⟩, hd1, hd2, hdg⟩ := hpre
  simp only [Disjoint] at hd2 hdg
  clear hd1 hp hp' hlc hc48 ho0 ho1 hd
  have hrc : s.mem.readLE (c.toNat + 2) 1 = 1 := by rw [Memory.readLE_one]; exact ho2
  janus_run [hsp, h0, h1, h2, h18, h28, h29, m_ret, m_fp, m_c, hrc] calls [og_summary]
  all_goals rw [hH]

end FvModexp.Arm64.RG
