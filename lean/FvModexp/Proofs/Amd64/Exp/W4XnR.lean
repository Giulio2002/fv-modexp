import FvModexp.Proofs.Amd64.Exp.W4XjR
import FvModexp.Proofs.Amd64.Exp.W4One

set_option autoImplicit false

/-!
# window-4 prologue (amd64): run pieces of the `x` normalisation (nat.go:1377-1386, fn+0x216 .. `xJ` = fn+0x3fe)
(agent expmc s55; twin of `Arm64.W4XnR`)

* `xnSplit`: `xnE` (fn+0x216, `CMPQ R8, BX; JLE`) → `j300` (`len x ≤ n`) or the entry of `stk.nat(len x - n + 1)`
  (path A, return `aSn1Ret`);
* `xnA1`: `aSn1Ret` → entry of `stk.nat(n)` (spills of `q` to 0x370/0x140/0x138, return `aSn2Ret`);
* `xnA2` (module `W4XnR2`): `aSn2Ret` → entry of `nat.div` (`q.div(stk, z2, x, m)`: `x`, `m` on the stack, return `aDivRet`);
* `xnA3`: `aDivRet` → `j300` (`x := r`);
* `xnJ`: `j300` (`CMPQ BX, R8; JLE`) → `xJ` (`n ≤ len x`) or the entry of `rr := stk.nat(n)` (path B, return
  `bSnRet`; spills 0x130 = `len x`, 0x368 = `xp`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

abbrev xnE : Nat := 6206070
abbrev aSn1Ret : Nat := 6206094
abbrev aSn2Ret : Nat := 6206139
abbrev aDivRet : Nat := 6206262
abbrev j300 : Nat := 6206304
abbrev bSnRet : Nat := 6206341

theorem toInt_lt_iff {a c : Nat} (ha : a < 2 ^ 63) (hc : c < 2 ^ 63) :
    ((BitVec.ofNat 64 a).toInt < (BitVec.ofNat 64 c).toInt) = (a < c) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega), BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
  simp only [BitVec.toNat_ofNat, eq_iff_iff]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnSplit {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp n st xl : Nat} {M : Memory}
    (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true) (hn : n ≤ 128) (hxl : xl < 2 ^ 40)
    (hst : st < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xnE) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (KJ : xl ≤ n → ∀ (S' : State), S'.rip = BitVec.ofNat 64 j300 → S'.mem = M → S'.regs = S.regs →
      S'.fsBase = S.fsBase → S'.xmm = S.xmm → S'.df = S.df → ReachesRet (LibW.program.link impl) ret S' Q)
    (KA : n < xl → ∀ (S' : State), S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 (xl - n + 1) →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.mem = M.writeLE (sp - 8) 8 aSn1Ret → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  by_cases hc : xl ≤ n
  · have hlt : ((BitVec.ofNat 64 n).toInt < (BitVec.ofNat 64 xl).toInt) = False := by
      rw [toInt_lt_iff (by omega) (by omega)]; simp only [eq_iff_iff, iff_false]; omega
    janus64_run [hlt] until [j300]
    exact KJ hc _ rfl rfl rfl rfl rfl rfl
  · have hlt : ((BitVec.ofNat 64 n).toInt < (BitVec.ofNat 64 xl).toInt) = True := by
      rw [toInt_lt_iff (by omega) (by omega)]; simp only [eq_iff_iff, iff_true]; omega
    janus64_run [hlt] until [snE]
    refine KA (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact h7 |
      (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

/-- the words `xnA1` writes -/
@[reducible] def xa1Ws (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x138, sp + 0x148), (sp + 0x370, sp + 0x378)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnA1 {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp n st qp ql qc : Nat} {M : Memory}
    (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true) (hn : n ≤ 128)
    (hacc2 : M.accessible (sp + 0x3c0) 0x38 false = true)
    (hqp : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64)
    (r3d8 : M.readLE (sp + 0x3d8) 8 = st) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 aSn1Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (KS : ∀ (S' : State), S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem (xa1Ws sp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = aSn2Ret → S'.mem.readLE (sp + 0x370) 8 = qp →
      S'.mem.readLE (sp + 0x140) 8 = ql → S'.mem.readLE (sp + 0x138) 8 = qc →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  janus64_run [r3d8, r3b0] until [snE]
  refine KS _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · have i : ∀ lo hi a, (lo, hi) ∈ xa1Ws sp → lo ≤ a → a + 8 ≤ hi → InRanges a 8 (xa1Ws sp) :=
      fun lo hi a hm h1 h2 => ⟨(lo, hi), hm, h1, h2⟩
    have m0 : (sp - 8, sp) ∈ xa1Ws sp := by simp only [xa1Ws, List.mem_cons, true_or]
    have m3 : (sp + 0x138, sp + 0x148) ∈ xa1Ws sp := by simp only [xa1Ws, List.mem_cons, true_or, or_true]
    have m4 : (sp + 0x370, sp + 0x378) ∈ xa1Ws sp := by simp only [xa1Ws, List.mem_cons, true_or, or_true]
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ (i _ _ _ m4 (by omega) (by omega))).writeLE_inRanges _
      (i _ _ _ m3 (by omega) (by omega))).writeLE_inRanges _ (i _ _ _ m3 (by omega) (by omega))).writeLE_inRanges _
      (i _ _ _ m0 (by omega) (by omega))
  · simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals
    simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
  all_goals exact Nat.mod_eq_of_lt (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnA3 {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp n st zp zc : Nat} {M : Memory}
    (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true)
    (hacc2 : M.accessible (sp + 0x3c0) 0x38 false = true)
    (r3d8 : M.readLE (sp + 0x3d8) 8 = st) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (r3c0 : M.readLE (sp + 0x3c0) 8 = zp) (r3d0 : M.readLE (sp + 0x3d0) 8 = zc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 aDivRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KJ : ∀ (S' : State), S'.rip = BitVec.ofNat 64 j300 → S'.mem = M → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 6 = S.regs 7 → S'.regs 8 = S.regs 6 → S'.regs 9 = S.regs 8 →
      S'.regs 3 = BitVec.ofNat 64 n → S'.regs 7 = BitVec.ofNat 64 st →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  janus64_run [r3d8, r3b0, r3c0, r3d0] until [j300]
  refine KJ _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals first | exact hsp | rfl

/-- the words `xnJ` writes on path B -/
@[reducible] def xbWs (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x130, sp + 0x138), (sp + 0x368, sp + 0x370)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnJ {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp n st xp xl : Nat} {M : Memory}
    (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true) (hn : n ≤ 128) (hxl : xl < 2 ^ 40)
    (hxp : xp < 2 ^ 64) (hst : st < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 j300) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (KX : n ≤ xl → ∀ (S' : State), S'.rip = BitVec.ofNat 64 xJ → S'.mem = M → S'.regs = S.regs →
      S'.fsBase = S.fsBase → S'.xmm = S.xmm → S'.df = S.df → ReachesRet (LibW.program.link impl) ret S' Q)
    (KB : xl < n → ∀ (S' : State), S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem (xbWs sp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = bSnRet → S'.mem.readLE (sp + 0x130) 8 = xl →
      S'.mem.readLE (sp + 0x368) 8 = xp → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  by_cases hc : n ≤ xl
  · have hlt : ((BitVec.ofNat 64 xl).toInt < (BitVec.ofNat 64 n).toInt) = False := by
      rw [toInt_lt_iff (by omega) (by omega)]; simp only [eq_iff_iff, iff_false]; omega
    janus64_run [hlt] until [xJ]
    exact KX hc _ rfl rfl rfl rfl rfl rfl
  · have hlt : ((BitVec.ofNat 64 xl).toInt < (BitVec.ofNat 64 n).toInt) = True := by
      rw [toInt_lt_iff (by omega) (by omega)]; simp only [eq_iff_iff, iff_true]; omega
    janus64_run [hlt] until [snE]
    refine KB (by omega) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
    all_goals first | exact h3 | skip
    · have i : ∀ lo hi a, (lo, hi) ∈ xbWs sp → lo ≤ a → a + 8 ≤ hi → InRanges a 8 (xbWs sp) :=
        fun lo hi a hm h1 h2 => ⟨(lo, hi), hm, h1, h2⟩
      have m0 : (sp - 8, sp) ∈ xbWs sp := by simp only [xbWs, List.mem_cons, true_or]
      have m1 : (sp + 0x130, sp + 0x138) ∈ xbWs sp := by simp only [xbWs, List.mem_cons, true_or, or_true]
      have m2 : (sp + 0x368, sp + 0x370) ∈ xbWs sp := by simp only [xbWs, List.mem_cons, true_or, or_true]
      exact (((MemFrame.refl _ _).writeLE_inRanges _ (i _ _ _ m1 (by omega) (by omega))).writeLE_inRanges _
        (i _ _ _ m2 (by omega) (by omega))).writeLE_inRanges _ (i _ _ _ m0 (by omega) (by omega))
    · simp only [Janus.Arm64.Memory.regions_writeLE]
    all_goals
      simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
    all_goals first | exact h7 | exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Amd64.W4Pro
