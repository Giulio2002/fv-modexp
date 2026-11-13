import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): the trivial cases (`J1` = fn+0xd8 → `J2` = fn+0x19c) (agent expmc s66; twin of
`Arm64.ExpN.triv`)

nat.go:648-668 (`RSP = t - 0x108`, `y` at `t + 8 …`, `m` at `t + 0x20 …`): `len m == 1 && m[0] == 1` → `return z[:0]`
(fn+0xf5); `len y == 0` → `setWord(1)` (fn+0x802); `len x == 0` → `return z[:0]` (fn+0x7db); `len x == 1 && x[0] == 1`
→ `setWord(1)` (fn+0x14c); else `J2`. The two `z[:0]` returns (result slots `t - 0x58 … t - 0x40`, `ADDQ $0x100, SP;
POPQ BP; RET`) are finished here (`F0`); the `setWord(1)` paths continue at their first instruction (`K1`). At `J2`:
`R15 = len y`, `R13 = m`, `R11 = len m`. Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem triv (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (F : State → Prop) (t bp xp xl yl mp n : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x108) 0x180 true = true)
    (hxl : xl < 2 ^ 64) (hxp : xp < 2 ^ 64)
    (hma : 0 < n → M.accessible mp 8 false = true) (hxa : 0 < xl → M.accessible xp 8 false = true)
    (rbp : M.readLE (t - 8) 8 = bp) (rra : M.readLE t 8 = ret0) (r10 : M.readLE (t + 0x10) 8 = yl)
    (r20 : M.readLE (t + 0x20) 8 = mp) (r28 : M.readLE (t + 0x28) 8 = n)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6189176) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (hmem : S.mem = M)
    (F0 : (n = 1 ∧ M.readLE mp 8 = 1) ∨ (¬(n = 1 ∧ M.readLE mp 8 = 1) ∧ yl ≠ 0 ∧ xl = 0) →
      ∀ s' : State, s'.regs 4 = BitVec.ofNat 64 (t + 8) → s'.regs 5 = BitVec.ofNat 64 bp →
      s'.regs 0 = S.regs 0 → s'.regs 3 = 0#64 → s'.regs 1 = S.regs 1 → s'.regs 14 = S.regs 14 →
      s'.fsBase = S.fsBase → s'.df = S.df → s'.xmm 15 = S.xmm 15 →
      MemFrame M s'.mem [(t - 0x58, t - 0x40)] → s'.mem.regions = M.regions → F s')
    (K1 : ¬(n = 1 ∧ M.readLE mp 8 = 1) → (yl = 0 ∨ (xl = 1 ∧ M.readLE xp 8 = 1)) →
      ∀ (S' : State) (pc0 : Nat), (pc0 = 6189292 ∨ pc0 = 6191010) →
      S'.rip = BitVec.ofNat 64 pc0 → S'.regs 4 = S.regs 4 → S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' (IsReturn F))
    (K2 : ¬(n = 1 ∧ M.readLE mp 8 = 1) → yl ≠ 0 → xl ≠ 0 → ¬(xl = 1 ∧ M.readLE xp 8 = 1) →
      ∀ S' : State, S'.rip = BitVec.ofNat 64 6189372 → S'.regs 4 = S.regs 4 →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = S.regs 7 →
      S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 →
      S'.regs 2 = S.regs 2 → S'.regs 12 = S.regs 12 → S'.regs 5 = S.regs 5 →
      S'.regs 15 = BitVec.ofNat 64 yl → S'.regs 13 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 n →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 →
      S'.mem = M → Reaches ((LibN.program.link impl).withExit ret0) S' (IsReturn F)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have es1 : BitVec.ofNat 64 (t - 0x108) + 256#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have a10 : t - 0x108 + 0x118 = t + 0x10 := by omega
  have a20 : t - 0x108 + 0x128 = t + 0x20 := by omega
  have a28 : t - 0x108 + 0x130 = t + 0x28 := by omega
  have hm8 : M.readLE mp 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hx8 : M.readLE xp 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := r10 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hn : n < 2 ^ 64 := r28 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := r20 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  subst hmem
  by_cases hn1 : n = 1
  · have hma' := hma (by omega)
    by_cases hx1 : xl = 1
    · have hxa' := hxa (by omega)
      janus64_run [es1, es2, es3, a10, a20, a28, rbp, rra, r10, r20, r28] until [6189372, 6189292, 6191010]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?mf ?_)
        | (refine K1 (by omega) (by omega) _ 6189292 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 6191010 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
      all_goals first | janus_frame | rfl
    · janus64_run [es1, es2, es3, a10, a20, a28, rbp, rra, r10, r20, r28] until [6189372, 6189292, 6191010]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?mf ?_)
        | (refine K1 (by omega) (by omega) _ 6189292 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 6191010 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
      all_goals first | janus_frame | rfl
  · by_cases hx1 : xl = 1
    · have hxa' := hxa (by omega)
      janus64_run [es1, es2, es3, a10, a20, a28, rbp, rra, r10, r20, r28] until [6189372, 6189292, 6191010]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?mf ?_)
        | (refine K1 (by omega) (by omega) _ 6189292 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 6191010 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
      all_goals first | janus_frame | rfl
    · janus64_run [es1, es2, es3, a10, a20, a28, rbp, rra, r10, r20, r28] until [6189372, 6189292, 6191010]
      all_goals first
        | (refine F0 (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?mf ?_)
        | (refine K1 (by omega) (by omega) _ 6189292 (Or.inl rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K1 (by omega) (by omega) _ 6191010 (Or.inr rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        | (refine K2 (by omega) (by omega) (by omega) (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
      all_goals first | janus_frame | rfl

end FvModexp.Amd64.ExpN
