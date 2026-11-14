import FvModexp.Proofs.Amd64.Exp.ModInvPostSub
import FvModexp.Proofs.Amd64.Exp.ModInvMS
import FvModexp.Proofs.Amd64.Exp.ModInvL0

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the runs around the loop round's `z = z.subMod2N(z, zz, e)` (agent infra
s58; twin of `Arm64/Exp/ModInvL5`)

* `runL5a` (`0x5ead39`): `e = i·64` (from `0xa8(SP')`) → `0(SP')` (`RSP_c + 8`), `z` (the `lsh` result) in
  `RAX, RBX, RCX` and `RDI, RSI, R8`, `zz` reloaded into `R9, R10, R11`, `subMod2N` at `0x5ead60`;
* `runL5b` (`0x5ead65`): the reloads (`x`, `stk`, `n`, `2i`, `zz`, `numWords`), `DX = BX`, then the loop head `J2`
  (`0x5eadaf`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runL5a (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp e p l c q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (he : e < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204729) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) 232 true = true)
    (hre : S.mem.readLE (sp - 224 + 168) 8 = e) (hrq : S.mem.readLE (sp - 224 + 200) 8 = q)
    (hrl : S.mem.readLE (sp - 224 + 104) 8 = ql) (hrc : S.mem.readLE (sp - 224 + 112) 8 = qc)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h3 : S.regs 3 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 6215840 →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 3 = BitVec.ofNat 64 l → S'.regs 1 = BitVec.ofNat 64 c →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
      S'.regs 9 = BitVec.ofNat 64 q → S'.regs 10 = BitVec.ofNat 64 ql → S'.regs 11 = BitVec.ofNat 64 qc →
      S'.mem = (S.mem.writeLE (sp - 224) 8 e).writeLE (sp - 224 - 8) 8 6204773 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  janus64_run [hre, hrq, hrl, hrc] until [6215840]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runL5b (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp st xp xl xc n i q ql qc nw : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204773) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true)
    (r1 : S.mem.readLE (sp - 224 + 264) 8 = xp) (r2 : S.mem.readLE (sp - 224 + 256) 8 = st)
    (r3 : S.mem.readLE (sp - 224 + 272) 8 = xl) (r4 : S.mem.readLE (sp - 224 + 280) 8 = xc)
    (r5 : S.mem.readLE (sp - 224 + 288) 8 = n) (r6 : S.mem.readLE (sp - 224 + 152) 8 = i)
    (r7 : S.mem.readLE (sp - 224 + 104) 8 = ql) (r8 : S.mem.readLE (sp - 224 + 112) 8 = qc)
    (r9 : S.mem.readLE (sp - 224 + 200) 8 = q) (r10 : S.mem.readLE (sp - 224 + 120) 8 = nw)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x4ef) → S'.regs 4 = S.regs 4 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 12 = BitVec.ofNat 64 i → S'.regs 0 = S.regs 0 → S'.regs 2 = S.regs 3 → S'.regs 1 = S.regs 1 →
      S'.regs 15 = BitVec.ofNat 64 q → S'.regs 13 = BitVec.ofNat 64 ql → S'.regs 11 = BitVec.ofNat 64 qc →
      S'.regs 3 = BitVec.ofNat 64 nw → S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 xp →
      S'.regs 8 = BitVec.ofNat 64 xl → S'.regs 9 = BitVec.ofNat 64 xc → S'.regs 10 = BitVec.ofNat 64 n →
      S'.mem = S.mem → ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  janus64_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] until [0x5ea8c0 + 0x4ef]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | skip

end FvModexp.Amd64.ModInv
