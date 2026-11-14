import FvModexp.Proofs.Amd64.Exp.ModInvL5

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the final round's run to `z = z.subMod2N(z, zz, n)` (agent infra s58;
twin of `Arm64/Exp/ModInvF5`'s run)

`runF5s` (`0x5eae99`): `n` (from `0x120(SP')` = `RSP + 64`) → `0(SP')` (`RSP_c + 8`), `z` in `RAX, RBX, RCX` and
`RDI, RSI, R8`, `zz` reloaded into `R9, R10, R11`, `subMod2N` at `0x5eaec0` (returns to `0x5eaec5`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runF5s (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp e p l c q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (he : e < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6205081) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true)
    (hre : S.mem.readLE (sp - 224 + 288) 8 = e) (hrq : S.mem.readLE (sp - 224 + 200) 8 = q)
    (hrl : S.mem.readLE (sp - 224 + 104) 8 = ql) (hrc : S.mem.readLE (sp - 224 + 112) 8 = qc)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h3 : S.regs 3 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 6215840 →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 3 = BitVec.ofNat 64 l → S'.regs 1 = BitVec.ofNat 64 c →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
      S'.regs 9 = BitVec.ofNat 64 q → S'.regs 10 = BitVec.ofNat 64 ql → S'.regs 11 = BitVec.ofNat 64 qc →
      S'.mem = (S.mem.writeLE (sp - 224) 8 e).writeLE (sp - 224 - 8) 8 6205125 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  janus64_run [hre, hrq, hrl, hrc] until [6215840]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

end FvModexp.Amd64.ModInv
