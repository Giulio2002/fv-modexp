import FvModexp.Proofs.Amd64.Exp.ModInvL1

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S3 → S4`, the runs to the second `zz = zz.trunc(zz, e)` (agent infra
s58; twin of `Arm64/Exp/ModInvL3` / `ModInvF4`)

* loop (`0x5eace5`): `e = i·64` from `0xa8(SP')` (`RSP - 56`), `trunc` at `0x5eacf6`, `S4` at `0x5eacfb`;
* final (`0x5eae45`): `e = n` from `0x120(SP')` (`RSP + 64`), `trunc` at `0x5eae56`, `S4` at `0x5eae5b`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- loop: `e` from `RSP - 56`, `nat.trunc`'s entry -/
theorem runL3 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp n q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204645) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true) (hrd : S.mem.readLE (sp - 224 + 168) 8 = n)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 q → S'.regs 6 = BitVec.ofNat 64 ql → S'.regs 8 = BitVec.ofNat 64 qc →
      S'.regs 9 = BitVec.ofNat 64 n →
      S'.mem = S.mem.writeLE (sp - 224 - 8) 8 6204667 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  rw [trunc_addr'] at K
  janus64_run [hrd] until [6188320]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- final: `e = n` from `RSP + 64`, `nat.trunc`'s entry -/
theorem runF4 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp n q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204997) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true) (hrd : S.mem.readLE (sp - 224 + 288) 8 = n)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 q → S'.regs 6 = BitVec.ofNat 64 ql → S'.regs 8 = BitVec.ofNat 64 qc →
      S'.regs 9 = BitVec.ofNat 64 n →
      S'.mem = S.mem.writeLE (sp - 224 - 8) 8 6205019 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  rw [trunc_addr'] at K
  janus64_run [hrd] until [6188320]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

end FvModexp.Amd64.ModInv
