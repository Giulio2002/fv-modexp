import FvModexp.Proofs.Amd64.Exp.ModInvPostM
import FvModexp.Proofs.Amd64.Exp.ModInvMS
import FvModexp.Proofs.Amd64.Exp.ModInvL0

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S2 → S3`, the runs to `zz = zz.mul(stk, zz, x[:k])` (agent infra s58;
twin of `Arm64/Exp/ModInvL2` / `ModInvF3`)

`y = x[:k]` goes to `0 / 8 / 0x10(SP')` (`RSP - 224 / - 216 / - 208` = `RSP_c + 8 / 16 / 24`):
* loop (`0x5eac8d`): `2i` → `0x98(SP')` (`RSP - 72`) before the call, `k = min(i, len x)` (`CMPQ; CMOVB`), `mul` at
  `0x5eace0`, `S3` at `0x5eace5`;
* final (`0x5eadfd`): `k = min(len x, numWords)` (`numWords` from `0x78(SP')` = `RSP - 104`), `mul` at `0x5eae40`,
  `S3` at `0x5eae45`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem mul_addr' : segAddr Extracted.program Q.NatMul.fn = 6228032 := by decide

/-- loop: the stack arguments and `2i` -/
@[reducible] def memL2 (sp : Nat) (M : Memory) (xp i k xc : Nat) : Memory :=
  ((((M.writeLE (sp - 224) 8 xp).writeLE (sp - 224 + 152) 8 (2 * i)).writeLE (sp - 224 + 8) 8 k).writeLE
    (sp - 224 + 16) 8 xc).writeLE (sp - 224 - 8) 8 6204645

/-- final: the stack arguments -/
@[reducible] def memF3 (sp : Nat) (M : Memory) (xp k xc : Nat) : Memory :=
  (((M.writeLE (sp - 224) 8 xp).writeLE (sp - 224 + 8) 8 k).writeLE (sp - 224 + 16) 8 xc).writeLE
    (sp - 224 - 8) 8 6204997

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- loop: `nat.mul`'s entry -/
theorem runL2 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp i st xp xl xc q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hi : i < 2 ^ 62) (hxl : xl < 2 ^ 64) (hxp : xp < 2 ^ 64)
    (hxc : xc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204557) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true) (hri : S.mem.readLE (sp - 224 + 152) 8 = i)
    (hrx : S.mem.readLE (sp - 224 + 264) 8 = xp) (hrl : S.mem.readLE (sp - 224 + 272) 8 = xl)
    (hrc : S.mem.readLE (sp - 224 + 280) 8 = xc) (hrs : S.mem.readLE (sp - 224 + 256) 8 = st)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatMul.fn) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 q → S'.regs 8 = BitVec.ofNat 64 ql →
      S'.regs 9 = BitVec.ofNat 64 qc →
      S'.mem = memL2 sp S.mem xp i (min i xl) xc →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  have e1 : i + i = 2 * i := by omega
  have e2 : (if xl < i then BitVec.ofNat 64 xl else BitVec.ofNat 64 i).toNat = min i xl := by
    split
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl]; omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  rw [mul_addr'] at K
  janus64_run [hri, hrx, hrl, hrc, hrs] until [6228032]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) |
    (janus64_simp; simp only [e1, e2, memL2])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- final: `nat.mul`'s entry -/
theorem runF3 (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp nw st xp xl xc q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hnw : nw < 2 ^ 64) (hxl : xl < 2 ^ 64) (hxp : xp < 2 ^ 64)
    (hxc : xc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6204925) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) (232 + 72) true = true) (hrn : S.mem.readLE (sp - 224 + 120) 8 = nw)
    (hrx : S.mem.readLE (sp - 224 + 264) 8 = xp) (hrl : S.mem.readLE (sp - 224 + 272) 8 = xl)
    (hrc : S.mem.readLE (sp - 224 + 280) 8 = xc) (hrs : S.mem.readLE (sp - 224 + 256) 8 = st)
    (h0 : S.regs 0 = BitVec.ofNat 64 q) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatMul.fn) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 q → S'.regs 8 = BitVec.ofNat 64 ql →
      S'.regs 9 = BitVec.ofNat 64 qc →
      S'.mem = memF3 sp S.mem xp (min nw xl) xc →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  have e2 : (if xl < nw then BitVec.ofNat 64 xl else BitVec.ofNat 64 nw).toNat = min nw xl := by
    split
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl]; omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw]; omega
  rw [mul_addr'] at K
  janus64_run [hrn, hrx, hrl, hrc, hrs] until [6228032]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2) |
    (janus64_simp; simp only [e2, memF3])

end FvModexp.Amd64.ModInv
