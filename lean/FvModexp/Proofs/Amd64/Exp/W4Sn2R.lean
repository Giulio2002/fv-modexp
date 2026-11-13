import FvModexp.Proofs.Amd64.Exp.W4DivR

set_option autoImplicit false

/-!
# window-4 prologue (amd64): `toSn2` — from the return of `nat.lsh` (`lshRet`, fn+0x54b) to `stk.nat`'s entry
(nat.go:1398-1399; agent expmc s53; twin of `Arm64.W4Sn2R`)

The spills `zz = lsh(…)` (`[0x188] = AX`, `[0xa0] = CX`, `[0x98] = BX`), then `AX = stk` (`[0x3d8]`), `BX = 2n`
(`[0x78]`) and the `CALL` (return address `sn2Ret` at `[sp - 8]`). The continuation gets the memory abstractly: a frame
of the four written words and their values.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- the return address of `nat.lsh` (fn+0x54b) -/
abbrev lshRet : Nat := 6206891

/-- the words `toSn2` writes -/
@[reducible] def sn2Ws (sp : Nat) : List (Nat × Nat) := [(sp - 8, sp), (sp + 0x98, sp + 0xa8), (sp + 0x188, sp + 0x190)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toSn2 {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp st zzp zzl zzc k2 : Nat} {M : Memory}
    (hal : sp % 8 = 0) (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true)
    (hacc2 : M.accessible (sp + 0x3c0) 0x20 false = true)
    (r3d8 : M.readLE (sp + 0x3d8) 8 = st) (r78 : M.readLE (sp + 0x78) 8 = k2)
    (hzzp : zzp < 2 ^ 64) (hzzl : zzl < 2 ^ 64) (hzzc : zzc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 lshRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h3 : S.regs 3 = BitVec.ofNat 64 zzl) (h1 : S.regs 1 = BitVec.ofNat 64 zzc)
    (KS : ∀ (S' : State), S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 k2 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem (sn2Ws sp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = sn2Ret → S'.mem.readLE (sp + 0x188) 8 = zzp → S'.mem.readLE (sp + 0xa0) 8 = zzc →
      S'.mem.readLE (sp + 0x98) 8 = zzl → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have b1 : st < 256 ^ 8 := r3d8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b2 : k2 < 256 ^ 8 := r78 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  janus64_run [r3d8, r78] until [snE]
  refine KS _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · have i0 : ∀ a, sp - 8 ≤ a → a + 8 ≤ sp → InRanges a 8 (sn2Ws sp) :=
      fun a h1 h2 => ⟨(sp - 8, sp), by simp only [sn2Ws, List.mem_cons, true_or], h1, h2⟩
    have i1 : ∀ a, sp + 0x98 ≤ a → a + 8 ≤ sp + 0xa8 → InRanges a 8 (sn2Ws sp) :=
      fun a h1 h2 => ⟨(sp + 0x98, sp + 0xa8), by simp only [sn2Ws, List.mem_cons, true_or, or_true], h1, h2⟩
    have i2 : ∀ a, sp + 0x188 ≤ a → a + 8 ≤ sp + 0x190 → InRanges a 8 (sn2Ws sp) :=
      fun a h1 h2 => ⟨(sp + 0x188, sp + 0x190), by simp only [sn2Ws, List.mem_cons, true_or, or_true], h1, h2⟩
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ (i2 _ (by omega) (by omega))).writeLE_inRanges _
      (i1 _ (by omega) (by omega))).writeLE_inRanges _ (i1 _ (by omega) (by omega))).writeLE_inRanges _
      (i0 _ (by omega) (by omega))
  · simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals
    simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
  all_goals first
    | exact Nat.mod_eq_of_lt b1 | exact Nat.mod_eq_of_lt b2
    | exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hzzp (by decide))
    | exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hzzc (by decide))
    | exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hzzl (by decide))

end FvModexp.Amd64.W4Pro
