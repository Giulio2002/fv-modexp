import FvModexp.Proofs.Amd64.Exp.P2DTzE
import FvModexp.Proofs.Amd64.Exp.P2DWinR

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `rshR` → the recursive call's entry (agent asm s69; twin of infra's arm64
`P2DRec.runRec`)

`y` re-stored at `[sp] / [sp + 8] / [sp + 0x10]` (memory `Mw M sp yp yl recR`), `R10 = logM - lo`, `RDI = st`,
`x = rsh`'s result (`RAX/RBX/RCX` → `RSI/R8/R9`), `z` reloaded from `0x60 / 0x98 / 0xa0`, return address `recR` pushed.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

abbrev recR : Nat := 0x5e9215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the run `rshR` → `fnE` -/
theorem runRec {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp zp zl zc st yp yl lm lo : Nat)
    (M : Memory) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0xd0 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 0xd8 true = true)
    (h78 : M.readLE (sp + 0x78) 8 = yp) (h80 : M.readLE (sp + 0x80) 8 = yl) (hc8 : M.readLE (sp + 0xc8) 8 = lm)
    (h58 : M.readLE (sp + 0x58) 8 = lo) (ha8 : M.readLE (sp + 0xa8) 8 = st) (h60 : M.readLE (sp + 0x60) 8 = zp)
    (h98 : M.readLE (sp + 0x98) 8 = zl) (ha0 : M.readLE (sp + 0xa0) 8 = zc) (hlo : lo ≤ lm)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 rshR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 fnE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 3 = BitVec.ofNat 64 zl → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = S.regs 0 → S'.regs 8 = S.regs 3 → S'.regs 9 = S.regs 1 →
      S'.regs 10 = BitVec.ofNat 64 (lm - lo) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = Mw M sp yp yl recR →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hlm : lm < 2 ^ 64 := by rw [← hc8]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hlo' : lo < 2 ^ 64 := by omega
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have esub : BitVec.ofNat 64 lm - BitVec.ofNat 64 lo = BitVec.ofNat 64 (lm - lo) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h78, h80, hc8, h58, ha8, h60, h98, ha0, e4, esub] until [0x5e8fa0]
  refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact xf)
