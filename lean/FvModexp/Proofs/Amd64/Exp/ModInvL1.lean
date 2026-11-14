import FvModexp.Proofs.Amd64.Exp.ModInvPost
import FvModexp.Proofs.Amd64.Exp.ModInvMS
import FvModexp.Proofs.Amd64.Exp.ModInvL0

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S1 → S2`, the first `zz = zz.trunc(zz, e)` (agent infra s58; twin of
`Arm64/Exp/ModInvL1` / `ModInvF2`)

* loop (`0x5eac65`): `e = i·64` (`i` from `RSP - 72`) → `0xa8(SP')` (`RSP - 56`), `trunc` at `0x5eac88`, `S2` at
  `0x5eac8d`;
* final (`0x5eade7`): `e = n` (from `0x120(SP')` = `RSP + 64`), `trunc` at `0x5eadf8`, `S2` at `0x5eadfd`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem trunc_addr' : segAddr Extracted.program fnTrunc = 6188320 := by decide

theorem shl6 {i : Nat} (h : i * 64 < 2 ^ 64) : BitVec.ofNat 64 i <<< 6 = BitVec.ofNat 64 (i * 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), show (2 : Nat) ^ 6 = 64 from rfl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- loop: `e = i·64` spilled, `nat.trunc`'s entry -/
theorem runL1 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp i q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hi : i * 64 < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204517) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) 232 true = true) (hrd : S.mem.readLE (sp - 224 + 152) 8 = i)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 q → S'.regs 6 = BitVec.ofNat 64 ql → S'.regs 8 = BitVec.ofNat 64 qc →
      S'.regs 9 = BitVec.ofNat 64 (i * 64) →
      S'.mem = (S.mem.writeLE (sp - 224 + 168) 8 (i * 64)).writeLE (sp - 224 - 8) 8 6204557 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  have hs := shl6 hi
  rw [trunc_addr'] at K
  janus64_run [hrd, hs] until [6188320]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- final: `e = n` (from `RSP + 64`), `nat.trunc`'s entry -/
theorem runF2 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp n q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204903) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true) (hrd : S.mem.readLE (sp - 224 + 288) 8 = n)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 q → S'.regs 6 = BitVec.ofNat 64 ql → S'.regs 8 = BitVec.ofNat 64 qc →
      S'.regs 9 = BitVec.ofNat 64 n →
      S'.mem = S.mem.writeLE (sp - 224 - 8) 8 6204925 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  rw [trunc_addr'] at K
  janus64_run [hrd] until [6188320]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

end FvModexp.Amd64.ModInv
