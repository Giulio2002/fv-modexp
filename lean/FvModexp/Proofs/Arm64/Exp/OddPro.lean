import FvModexp.Proofs.Arm64.Exp.LibOdd
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNNOdd` (arm64): prologue and dispatch (fn+0x0 .. the window's entry), and the epilogue

`pro`: stack check (falls through), `MOVD.W R30, -128(RSP)`, saved FP at `SP - 136`, the four argument spills to
`SP + 8, + 40, + 64, + 88` (Go's spill slots of `z`, `x`, `y`, `m` in the caller's frame), `CMP $1, R8; BLE`:
`len(y) > 1` → `CALL expNNOddMontgomeryWindowSize4` (return `r4`), else `CALL expNNOddMontgomeryWindowSize2`
(return `r2`). Continuation form. `epi`: from a return point (`r4`/`r2`) the reloads of FP/LR and `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpOdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem pro (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibOdd.program.link impl) ret0)
    (Q : Outcome → Prop) (sp g ylen ret : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1168 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 920) 248 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 1056)
    (hyl : ylen < 2 ^ 40) (hret48 : ret < 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1798352) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h8 : S.regs 8 = BitVec.ofNat 64 ylen) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (K4 : 1 < ylen → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 1798512 → S'.sp = BitVec.ofNat 64 (sp + 928) →
      
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 → S'.regs 12 = S.regs 12 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 30 = BitVec.ofNat 64 1798404 →
      S'.mem = M' → MemFrame M M' [(sp + 920, sp + 936), (sp + 1064, sp + 1152)] → M'.regions = M.regions →
      M'.readLE (sp + 920) 8 = r29.toNat → M'.readLE (sp + 928) 8 = ret →
      Reaches ((LibOdd.program.link impl).withExit ret0) S' Q)
    (K2 : ylen ≤ 1 → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 1801904 → S'.sp = BitVec.ofNat 64 (sp + 928) →
      
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 → S'.regs 12 = S.regs 12 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 30 = BitVec.ofNat 64 1798420 →
      S'.mem = M' → MemFrame M M' [(sp + 920, sp + 936), (sp + 1064, sp + 1152)] → M'.regions = M.regions →
      M'.readLE (sp + 920) 8 = r29.toNat → M'.readLE (sp + 928) 8 = ret →
      Reaches ((LibOdd.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibOdd.program.link impl).withExit ret0) S Q := by
  generalize e18 : S.regs 18 = x18 at K4 K2
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 1056) - 128#64 = BitVec.ofNat 64 (sp + 928) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 928) - 8#64 = BitVec.ofNat 64 (sp + 920) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h63 : (BitVec.ofNat 64 ylen).getLsbD 63 = false :=
    getLsbD63_false _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  have hr29 : r29.toNat < 2 ^ 64 := r29.isLt
  by_cases hy : 1 < ylen
  · janus_run [es1, es2, h63] until [1798512]
    refine K4 hy _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?r1 ?r2
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 920, sp + 936)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1064, sp + 1152)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
  · janus_run [es1, es2, h63] until [1801904]
    refine K2 (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?r1 ?r2
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 920, sp + 936)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1064, sp + 1152)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from a window's return point: reload FP and LR, pop the frame, `RET` -/
theorem epi (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibOdd.program.link impl) ret0)
    (F : State → Prop) (sp f r : Nat) (M : Memory) (hr : r = 1798404 ∨ r = 1798420)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1168 ≤ 2 ^ 48) (hacc : M.accessible (sp + 920) 16 false = true)
    (h29v : M.readLE (sp + 920) 8 = f) (h30v : M.readLE (sp + 928) 8 = ret0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 r) (hsp : S.sp = BitVec.ofNat 64 (sp + 928)) (hmem : S.mem = M)
    (hK : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 1056) → s'.regs 29 = BitVec.ofNat 64 f →
      s'.regs 0 = S.regs 0 → s'.regs 1 = S.regs 1 → s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 →
      s'.regs 28 = S.regs 28 → s'.mem = M → F s') :
    Reaches ((LibOdd.program.link impl).withExit ret0) S (IsReturn F) := by
  have es : BitVec.ofNat 64 (sp + 928) - 8#64 = BitVec.ofNat 64 (sp + 920) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 928) + 128#64 = BitVec.ofNat 64 (sp + 1056) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rcases hr with rfl | rfl
  all_goals
    janus_run [es, es2, h29v, h30v]
    refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | rfl | (janus_simp; done) | skip

end FvModexp.Arm64.ExpOdd
