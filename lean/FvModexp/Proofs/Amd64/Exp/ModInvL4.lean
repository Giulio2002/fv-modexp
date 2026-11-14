import FvModexp.Proofs.Amd64.Exp.ModInvPostL
import FvModexp.Proofs.Amd64.Exp.ModInvMS
import FvModexp.Proofs.Amd64.Exp.ModInvL0

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S4 → S5`, the runs to `z = z.lsh(z, 1)` (agent infra s58; twin of
`Arm64/Exp/ModInvL4` / `ModInvF5`'s first part)

`zz` → `0xc8 / 0x68 / 0x70(SP')` (`RSP - 24 / - 120 / - 112`), `z` reloaded from its slots, `R9 = 1`:
* loop (`0x5eacfb`): `lsh` at `0x5ead34`, `S5` at `0x5ead39`;
* final (`0x5eae5b`): `lsh` at `0x5eae94`, `S5` at `0x5eae99`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem lsh_addr' : segAddr Extracted.program Lsh.fn = 6186528 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- loop: `zz` spilled, `z` reloaded, `nat.lsh`'s entry -/
theorem runL4 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp p l c q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hq : q < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204667) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) 232 true = true)
    (hrp : S.mem.readLE (sp - 224 + 208) 8 = p) (hrl : S.mem.readLE (sp - 224 + 176) 8 = l)
    (hrc : S.mem.readLE (sp - 224 + 184) 8 = c)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Lsh.fn) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 3 = BitVec.ofNat 64 l → S'.regs 1 = BitVec.ofNat 64 c →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
      S'.regs 9 = BitVec.ofNat 64 1 →
      S'.mem = (((S.mem.writeLE (sp - 224 + 200) 8 q).writeLE (sp - 224 + 104) 8 ql).writeLE (sp - 224 + 112) 8
        qc).writeLE (sp - 224 - 8) 8 6204729 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  rw [lsh_addr'] at K
  janus64_run [hrp, hrl, hrc] until [6186528]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- final: `zz` spilled, `z` reloaded, `nat.lsh`'s entry -/
theorem runF5a (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp p l c q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hq : q < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6205019) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) 232 true = true)
    (hrp : S.mem.readLE (sp - 224 + 208) 8 = p) (hrl : S.mem.readLE (sp - 224 + 176) 8 = l)
    (hrc : S.mem.readLE (sp - 224 + 184) 8 = c)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Lsh.fn) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 3 = BitVec.ofNat 64 l → S'.regs 1 = BitVec.ofNat 64 c →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
      S'.regs 9 = BitVec.ofNat 64 1 →
      S'.mem = (((S.mem.writeLE (sp - 224 + 200) 8 q).writeLE (sp - 224 + 104) 8 ql).writeLE (sp - 224 + 112) 8
        qc).writeLE (sp - 224 - 8) 8 6205081 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  rw [lsh_addr'] at K
  janus64_run [hrp, hrl, hrc] until [6186528]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

end FvModexp.Amd64.ModInv
