import FvModexp.Proofs.Amd64.Exp.W2Div

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `toDiv` — from the return of `stk.nat(2n)` #2 (`sn2Ret`, fn+0x5af) to `nat.div`'s entry
(agent expmc s52; twin of `Arm64.W2DivR`)

The stack arguments `u = zz` (`[0x188]`, `[0x98]`, `[0xa0]`) and `v = m` (`[0x290]`, `[0x298]`, `[0x2a0]`) are stored
at `[sp, sp + 48)`, `DI = stk` (`[0x2c0]`), `SI/R8/R9 = RR` (`[0x190]`, 1, `[0xa8]`); `q` stays in `AX/BX/CX`. The
`CALL` pushes `divRet` at `[sp - 8]`. The continuation gets the memory abstractly: a frame `[(sp - 8, sp + 48)]` and
the seven written words.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

/-- the return address of the second `stk.nat(2n)` (fn+0x5af) -/
abbrev sn2Ret : Nat := 6212015

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toDiv {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp st rrp zzp zzl zzc mp n mc : Nat} {M : Memory}
    (hal : sp % 16 = 0) (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x2a8 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x2a8) true = true)
    (hacc2 : M.accessible (sp + 0x2a8) 0x20 false = true)
    (r3d8 : M.readLE (sp + 0x2c0) 8 = st) (r190 : M.readLE (sp + 0x198) 8 = rrp)
    (ra8 : M.readLE (sp + 0xa8) 8 = 2 * n) (r188 : M.readLE (sp + 0x190) 8 = zzp)
    (r98 : M.readLE (sp + 0x98) 8 = zzl) (ra0 : M.readLE (sp + 0xa0) 8 = zzc)
    (r3a8 : M.readLE (sp + 0x290) 8 = mp) (r3b0 : M.readLE (sp + 0x298) 8 = n) (r3b8 : M.readLE (sp + 0x2a0) 8 = mc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 sn2Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KD : ∀ (S' : State), S'.rip = BitVec.ofNat 64 divE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 rrp → S'.regs 8 = BitVec.ofNat 64 1 →
      S'.regs 9 = BitVec.ofNat 64 (2 * n) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem [(sp - 8, sp + 48)] → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = divRet → S'.mem.readLE sp 8 = zzp → S'.mem.readLE (sp + 8) 8 = zzl →
      S'.mem.readLE (sp + 16) 8 = zzc → S'.mem.readLE (sp + 24) 8 = mp → S'.mem.readLE (sp + 32) 8 = n →
      S'.mem.readLE (sp + 40) 8 = mc → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have b1 : zzp < 256 ^ 8 := r188 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b2 : zzl < 256 ^ 8 := r98 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b3 : zzc < 256 ^ 8 := ra0 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b4 : mp < 256 ^ 8 := r3a8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b5 : n < 256 ^ 8 := r3b0 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have b6 : mc < 256 ^ 8 := r3b8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  janus64_run [r3d8, r190, ra8, r188, r98, ra0, r3a8, r3b0, r3b8] until [divE]
  refine KD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · have hw : ∀ a, sp - 8 ≤ a → a + 8 ≤ sp + 48 → InRanges a 8 [(sp - 8, sp + 48)] :=
      fun a h1 h2 => ⟨(sp - 8, sp + 48), List.mem_singleton_self _, h1, h2⟩
    exact ((((((((MemFrame.refl _ _).writeLE_inRanges _ (hw _ (by omega) (by omega))).writeLE_inRanges _
      (hw _ (by omega) (by omega))).writeLE_inRanges _ (hw _ (by omega) (by omega))).writeLE_inRanges _
      (hw _ (by omega) (by omega))).writeLE_inRanges _ (hw _ (by omega) (by omega))).writeLE_inRanges _
      (hw _ (by omega) (by omega))).writeLE_inRanges _ (hw _ (by omega) (by omega)))
  · simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals
    simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
  · exact Nat.mod_eq_of_lt b1
  · exact Nat.mod_eq_of_lt b2
  · exact Nat.mod_eq_of_lt b3
  · exact Nat.mod_eq_of_lt b4
  · exact Nat.mod_eq_of_lt b5
  · exact Nat.mod_eq_of_lt b6

end FvModexp.Amd64.W2Pro
