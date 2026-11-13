import FvModexp.Proofs.Amd64.Exp.W2LshR
import FvModexp.Proofs.Amd64.Exp.W2K0

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `toSn1` — from the Newton loop's exit `kExit` (fn+0x4f2) to the entry of
`stk.nat(2n)` #1 (nat.go:1522, 1276, 1530; agent expmc s62; port of `Amd64.W4Pro.toSn1`)

Spills `[0x258] = SI`, `[0x140] = R8`, `[0x138] = R9`, `[0xd8] = R13` (`t`, the Newton value), `BX = 2·BX`,
`[0x78] = BX`, `AX = DI` (the stack) and the `CALL` (return address `sn1Ret` at `[sp - 8]`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

/-- the words `toSn1` writes -/
@[reducible] def sn1Ws (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x78, sp + 0x80), (sp + 0xd8, sp + 0xe0), (sp + 0x138, sp + 0x148), (sp + 0x258, sp + 0x260)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toSn1 {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp n st xp xc t : Nat} {M : Memory}
    (hal : sp % 16 = 0) (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x2a8 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x2a8) true = true) (hn : n ≤ 128)
    (hst : st < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxc : xc < 2 ^ 64) (ht : t < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 kExit) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h8 : S.regs 8 = BitVec.ofNat 64 n) (h6 : S.regs 6 = BitVec.ofNat 64 xp)
    (h13 : S.regs 13 = BitVec.ofNat 64 t) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (KS : ∀ (S' : State), S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 (2 * n) →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem (sn1Ws sp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = sn1Ret → S'.mem.readLE (sp + 0x78) 8 = 2 * n →
      S'.mem.readLE (sp + 0xd8) 8 = t → S'.mem.readLE (sp + 0x140) 8 = n → S'.mem.readLE (sp + 0x138) 8 = xc →
      S'.mem.readLE (sp + 0x258) 8 = xp → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have e2 : BitVec.ofNat 64 n + BitVec.ofNat 64 n = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus64_run [e2] until [snE]
  refine KS _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · have i : ∀ lo hi a, (lo, hi) ∈ sn1Ws sp → lo ≤ a → a + 8 ≤ hi → InRanges a 8 (sn1Ws sp) :=
      fun lo hi a hm h1 h2 => ⟨(lo, hi), hm, h1, h2⟩
    have m0 : (sp - 8, sp) ∈ sn1Ws sp := by simp only [sn1Ws, List.mem_cons, true_or]
    have m1 : (sp + 0x78, sp + 0x80) ∈ sn1Ws sp := by simp only [sn1Ws, List.mem_cons, true_or, or_true]
    have m2 : (sp + 0xd8, sp + 0xe0) ∈ sn1Ws sp := by simp only [sn1Ws, List.mem_cons, true_or, or_true]
    have m3 : (sp + 0x138, sp + 0x148) ∈ sn1Ws sp := by simp only [sn1Ws, List.mem_cons, true_or, or_true]
    have m4 : (sp + 0x258, sp + 0x260) ∈ sn1Ws sp := by simp only [sn1Ws, List.mem_cons, true_or, or_true]
    exact ((((((MemFrame.refl _ _).writeLE_inRanges _ (i _ _ _ m4 (by omega) (by omega))).writeLE_inRanges _
      (i _ _ _ m3 (by omega) (by omega))).writeLE_inRanges _ (i _ _ _ m3 (by omega) (by omega))).writeLE_inRanges _
      (i _ _ _ m2 (by omega) (by omega))).writeLE_inRanges _ (i _ _ _ m1 (by omega) (by omega))).writeLE_inRanges _
      (i _ _ _ m0 (by omega) (by omega))
  · simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals
    simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
  all_goals exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Amd64.W2Pro
