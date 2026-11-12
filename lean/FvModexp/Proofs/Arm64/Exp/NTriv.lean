import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64): the trivial cases (`J1` = fn+0x8c → `J2` = fn+0x114)

nat.go:648-668: `len m == 1 && m[0] == 1` → `return z[:0]` (fn+0xb4); `len y == 0` → `setWord(1)` (fn+0x538);
`len x == 0` → `return z[:0]` (fn+0x520); `len x == 1 && x[0] == 1` → `setWord(1)` (fn+0xd4); else `J2`.
The two `z[:0]` returns are finished here (`F0`); the `setWord(1)` paths continue at their first instruction (`K1`,
then `ExpN.one`). Continuation form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem triv (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    (sp f29 xp xl yl mp n : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 1048) 360 true = true)
    (hxl : xl < 2 ^ 64) (hyl : yl < 2 ^ 64) (hn : n < 2 ^ 64) (hxp : xp < 2 ^ 64) (hmp : mp < 2 ^ 64)
    (hma : 0 < n → M.accessible mp 8 false = true) (hxa : 0 < xl → M.accessible xp 8 false = true)
    (h29v : M.readLE (sp + 1048) 8 = f29) (h30v : M.readLE (sp + 1056) 8 = ret0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1786684) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 n) (hmem : S.mem = M)
    (F0 : (n = 1 ∧ M.readLE mp 8 = 1) ∨ (¬(n = 1 ∧ M.readLE mp 8 = 1) ∧ yl ≠ 0 ∧ xl = 0) →
      ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 1312) → s'.regs 29 = BitVec.ofNat 64 f29 →
      s'.regs 0 = S.regs 0 → s'.regs 1 = 0#64 → s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 →
      s'.regs 28 = S.regs 28 → MemFrame M s'.mem [(sp + 1232, sp + 1256)] → s'.mem.regions = M.regions → F s')
    (K1 : ¬(n = 1 ∧ M.readLE mp 8 = 1) → (yl = 0 ∨ (xl = 1 ∧ M.readLE xp 8 = 1)) →
      ∀ (S' : State) (pc0 : Nat), (pc0 = 1786756 ∨ pc0 = 1787880) →
      S'.pc = BitVec.ofNat 64 pc0 → S'.sp = S.sp → S'.regs 0 = S.regs 0 → S'.regs 2 = S.regs 2 →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' (IsReturn F))
    (K2 : ¬(n = 1 ∧ M.readLE mp 8 = 1) → yl ≠ 0 → xl ≠ 0 → ¬(xl = 1 ∧ M.readLE xp 8 = 1) →
      ∀ S' : State, S'.pc = BitVec.ofNat 64 1786820 → S'.sp = S.sp →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 →
      S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 →
      S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 →
      S'.regs 12 = S.regs 12 → S'.regs 13 = S.regs 13 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.mem = M → Reaches ((LibN.program.link impl).withExit ret0) S' (IsReturn F)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have es : BitVec.ofNat 64 (sp + 1056) - 8#64 = BitVec.ofNat 64 (sp + 1048) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 1056) + 256#64 = BitVec.ofNat 64 (sp + 1312) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hm8 : M.readLE mp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have hx8 : M.readLE xp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  by_cases hn1 : n = 1
  · have hma' := hma (by omega)
    by_cases hx1 : xl = 1
    · have hxa' := hxa (by omega)
      janus_run [es, es2, h29v, h30v] until [1786820, 1786756, 1787880]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1786756 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1787880 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus_simp; done) | skip
      all_goals first
        | (repeat (first
            | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega))
           exact MemFrame.refl _ _)
        | rfl
    · janus_run [es, es2, h29v, h30v] until [1786820, 1786756, 1787880]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1786756 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1787880 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus_simp; done) | skip
      all_goals first
        | (repeat (first
            | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega))
           exact MemFrame.refl _ _)
        | rfl
  · by_cases hx1 : xl = 1
    · have hxa' := hxa (by omega)
      janus_run [es, es2, h29v, h30v] until [1786820, 1786756, 1787880]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1786756 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1787880 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus_simp; done) | skip
      all_goals first
        | (repeat (first
            | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega))
           exact MemFrame.refl _ _)
        | rfl
    · janus_run [es, es2, h29v, h30v] until [1786820, 1786756, 1787880]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1786756 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 1787880 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus_simp; done) | skip
      all_goals first
        | (repeat (first
            | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega))
           exact MemFrame.refl _ _)
        | rfl

end FvModexp.Arm64.ExpN
