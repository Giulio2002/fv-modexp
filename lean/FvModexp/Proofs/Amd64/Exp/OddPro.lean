import FvModexp.Proofs.Amd64.Exp.LibOdd
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.expNNOdd` (amd64): prologue and dispatch (entry → a window's entry), and the epilogue (agent expmc s64)

`pro` (entry `RSP = t`): stack check (falls through), `PUSHQ BP` (`[t - 8]`), `SUBQ $0x68` (`RSP = t - 0x70`), spills
`AX → t + 0x38`, `SI → t + 0x58`, `CMPQ [t + 0x10], $1; JLE`: `len(y) > 1` → the six words `[t + 8, t + 0x38)` (`y`, `m`)
copied to `[t - 0x70, t - 0x40)` and `CALL expNNOddMontgomeryWindowSize4` (return `r4` at `t - 0x78`), else the same
with `expNNOddMontgomeryWindowSize2` (return `r2`). Continuation form. `epi`: from a return point (`RSP = t - 0x70`)
`ADDQ $0x68, SP; POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpOdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem pro (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibOdd.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t g yp ylen mp n mc : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x80 ≤ t) (ht2 : t + 0x70 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x78) 0xe8 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < t)
    (hyl : ylen < 2 ^ 40)
    (r08 : M.readLE (t + 8) 8 = yp) (r10 : M.readLE (t + 0x10) 8 = ylen) (r20 : M.readLE (t + 0x20) 8 = mp)
    (r28 : M.readLE (t + 0x28) 8 = n) (r30 : M.readLE (t + 0x30) 8 = mc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6205248) (hsp : S.regs 4 = BitVec.ofNat 64 t)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (K4 : 1 < ylen → ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 6205536 → S'.regs 4 = BitVec.ofNat 64 (t - 0x78) →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = S.regs 7 →
      S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x78, t), (t + 0x38, t + 0x60)] → M'.regions = M.regions →
      M'.readLE (t - 0x78) 8 = 6205367 → M'.readLE (t - 8) 8 = (S.regs 5).toNat →
      M'.readLE (t - 0x70) 8 = yp → M'.readLE (t - 0x68) 8 = ylen → M'.readLE (t - 0x58) 8 = mp →
      M'.readLE (t - 0x50) 8 = n → M'.readLE (t - 0x48) 8 = mc →
      Reaches ((LibOdd.program.link impl).withExit ret0) S' Q)
    (K2 : ylen ≤ 1 → ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 6210560 → S'.regs 4 = BitVec.ofNat 64 (t - 0x78) →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = S.regs 7 →
      S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x78, t), (t + 0x38, t + 0x60)] → M'.regions = M.regions →
      M'.readLE (t - 0x78) 8 = 6205445 → M'.readLE (t - 8) 8 = (S.regs 5).toNat →
      M'.readLE (t - 0x70) 8 = yp → M'.readLE (t - 0x68) 8 = ylen → M'.readLE (t - 0x58) 8 = mp →
      M'.readLE (t - 0x50) 8 = n → M'.readLE (t - 0x48) 8 = mc →
      Reaches ((LibOdd.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibOdd.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := r08 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := r20 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hn : n < 2 ^ 64 := r28 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := r30 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have h5 : (S.regs 5).toNat < 2 ^ 64 := (S.regs 5).isLt
  have es1 : BitVec.ofNat 64 t - 8#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) - 104#64 = BitVec.ofNat 64 (t - 0x70) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (t - 0x70) - 8#64 = BitVec.ofNat 64 (t - 0x78) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have a08 : t - 0x70 + 0x78 = t + 8 := by omega
  have a10 : t - 0x70 + 0x80 = t + 0x10 := by omega
  have a18 : t - 0x70 + 0x88 = t + 0x18 := by omega
  have a20 : t - 0x70 + 0x90 = t + 0x20 := by omega
  have a28 : t - 0x70 + 0x98 = t + 0x28 := by omega
  have a30 : t - 0x70 + 0xa0 = t + 0x30 := by omega
  subst r08 r10 r20 r28 r30 hmem
  by_cases hy : 1 < S.mem.readLE (t + 0x10) 8
  · janus64_run [es1, es2, es3, a08, a10, a18, a20, a28, a30] until [6205536]
    all_goals
      refine K4 hy _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by
        try dsimp only
        repeat (first
          | refine MemFrame.writeLE ?_ _ (r := (t - 0x78, t)) (by simp) (by simp only; omega) (by simp only; omega)
          | refine MemFrame.writeLE ?_ _ (r := (t + 0x38, t + 0x60)) (by simp) (by simp only; omega) (by simp only; omega))
        exact MemFrame.refl _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus64_simp; done) | skip
    all_goals first | omega | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod]; omega)
  · janus64_run [es1, es2, es3, a08, a10, a18, a20, a28, a30] until [6210560]
    all_goals
      refine K2 (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by
        try dsimp only
        repeat (first
          | refine MemFrame.writeLE ?_ _ (r := (t - 0x78, t)) (by simp) (by simp only; omega) (by simp only; omega)
          | refine MemFrame.writeLE ?_ _ (r := (t + 0x38, t + 0x60)) (by simp) (by simp only; omega) (by simp only; omega))
        exact MemFrame.refl _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus64_simp; done) | skip
    all_goals first | omega | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from a window's return point (`RSP = t - 0x70`): `ADDQ $0x68, SP; POPQ BP; RET` -/
theorem epi (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibOdd.program.link impl) ret0)
    (F : State → Prop) (t bp r : Nat) (hr : r = 6205367 ∨ r = 6205445)
    (ht1 : 0x80 ≤ t) (ht2 : t + 0x70 ≤ 2 ^ 48)
    (S : State) (hacc : S.mem.accessible (t - 8) 16 false = true)
    (hpc : S.rip = BitVec.ofNat 64 r) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x70))
    (sbp : S.mem.readLE (t - 8) 8 = bp) (sra : S.mem.readLE t 8 = ret0)
    (KB : ∀ (s4 : State), s4.mem = S.mem → s4.regs 4 = BitVec.ofNat 64 (t + 8) → s4.regs 0 = S.regs 0 →
      s4.regs 3 = S.regs 3 → s4.regs 1 = S.regs 1 →
      s4.regs 5 = BitVec.ofNat 64 bp → s4.regs 14 = S.regs 14 → s4.fsBase = S.fsBase → s4.df = S.df →
      s4.xmm 15 = S.xmm 15 → F s4) :
    Reaches ((LibOdd.program.link impl).withExit ret0) S (IsReturn F) := by
  have es1 : BitVec.ofNat 64 (t - 0x70) + 104#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rcases hr with rfl | rfl
  all_goals
    janus64_run [es1, es2, es3, sbp, sra]
    all_goals first
      | exact KB _ rfl (by simp only [setRegF_apply]; rfl) (by simp only [setRegF_apply]; rfl)
          (by simp only [setRegF_apply]; rfl) (by simp only [setRegF_apply]; rfl)
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) (by simp only [setRegF_apply]; rfl) rfl rfl rfl
      | skip

end FvModexp.Amd64.ExpOdd
