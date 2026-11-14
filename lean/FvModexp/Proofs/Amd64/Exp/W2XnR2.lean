import FvModexp.Proofs.Amd64.Exp.W2XnR
import FvModexp.Proofs.Amd64.Exp.W2Seg

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `xnA2` — from the return of `z2 := stk.nat(n)` (`aSn2Ret`, fn+0x272) to the entry of
`nat.div` (`q.div(stk, z2, x, m)`, nat.go:1378; agent expmc s55): the stack arguments `x`, `m` at `[sp, sp + 48)`,
`DI = stk`, `SI/R8/R9 = z2`, `AX/BX/CX = q` (from the spills 0x258/0x140/0x138), return address `aDivRet`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnA2 {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp n mp mc st qp ql qc xp xl xc z2p : Nat} {M : Memory}
    (hmp : mp < 2 ^ 64) (hmc : mc < 2 ^ 64) (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hql : ql < 2 ^ 64)
    (hqc : qc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x2a8 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x2a8) true = true) (hn : n ≤ 128)
    (hacc2 : M.accessible (sp + 0x2a8) 0x38 false = true) (hz2p : z2p < 2 ^ 64)
    (r3d8 : M.readLE (sp + 0x2c0) 8 = st) (r3b0 : M.readLE (sp + 0x298) 8 = n)
    (r3a8 : M.readLE (sp + 0x290) 8 = mp) (r3b8 : M.readLE (sp + 0x2a0) 8 = mc)
    (r3e0 : M.readLE (sp + 0x2c8) 8 = xp) (r3e8 : M.readLE (sp + 0x2d0) 8 = xl) (r3f0 : M.readLE (sp + 0x2d8) 8 = xc)
    (r370 : M.readLE (sp + 0x258) 8 = qp) (r140 : M.readLE (sp + 0x140) 8 = ql) (r138 : M.readLE (sp + 0x138) 8 = qc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 aSn2Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z2p) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (KD : ∀ (S' : State), S'.rip = BitVec.ofNat 64 6217504 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 qp → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 z2p → S'.regs 8 = BitVec.ofNat 64 n →
      S'.regs 9 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem [(sp - 8, sp + 0x30)] → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = aDivRet → S'.mem.readLE sp 8 = xp → S'.mem.readLE (sp + 8) 8 = xl →
      S'.mem.readLE (sp + 16) 8 = xc → S'.mem.readLE (sp + 24) 8 = mp → S'.mem.readLE (sp + 32) 8 = n →
      S'.mem.readLE (sp + 40) 8 = mc →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 6217504) ?_
  janus64_run [r3d8, r3b0, r3a8, r3b8, r3e0, r3e8, r3f0, r370, r140, r138] until [6217504]
  refine KD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · have i : ∀ a, sp - 8 ≤ a → a + 8 ≤ sp + 0x30 → InRanges a 8 [(sp - 8, sp + 0x30)] :=
      fun a h1 h2 => ⟨(sp - 8, sp + 0x30), by simp only [List.mem_cons, true_or], h1, h2⟩
    exact (((((((MemFrame.refl _ _).writeLE_inRanges _ (i _ (by omega) (by omega))).writeLE_inRanges _
      (i _ (by omega) (by omega))).writeLE_inRanges _ (i _ (by omega) (by omega))).writeLE_inRanges _
      (i _ (by omega) (by omega))).writeLE_inRanges _ (i _ (by omega) (by omega))).writeLE_inRanges _
      (i _ (by omega) (by omega))).writeLE_inRanges _ (i _ (by omega) (by omega))
  · simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals
    simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
  all_goals exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Amd64.W2Pro
