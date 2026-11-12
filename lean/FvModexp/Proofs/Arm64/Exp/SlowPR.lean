import FvModexp.Proofs.Arm64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the pure runs of the prologue `z = z.set(x)` (agent expmc; pattern of infra's EvSetR)

nat.go:732-733, 58-69, 93-94 (inlined `z.make(len x)` + `copy(z, x)`):
* `runE`: `fnE` → stack guard (`SUB $304`), frame `sp = SP - 432`, `STP (R29, R30), -8(sp)`, argument spills
  `440` (`z.ptr`), `464..536`; `CMP R5, R2; BLT`: `len x ≤ cap z` → `MV` (`fnE + 0xec`, reuse); else
  `makeslice(Word, 1, 1)` (`len x = 1`, return `mk1R`) or `112 := len x + 4`, `makeslice(Word, len x, len x + 4)`
  (return `mk2R`);
* `runM1` / `runMN`: the two `makeslice` returns → `MV` (arguments reloaded from the spills);
* `runMV`: `MV` → same pointer (`CMP R0, R4; BEQ`) → `PV` (`fnE + 0x144`), else `144 := cap`, `136 := len`,
  `344 := ptr`, `memmove(z, x, 8 · len x)` (return `mvR`);
* `runMvR`: `mvR` → `PV` (reloads).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- `runtime.makeslice`'s / `runtime.memmove`'s contract addresses -/
abbrev mkA : Nat := 587344
abbrev mvA : Nat := 609408

theorem mkA_eq : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem mvA_eq : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide

/-- the join `MV` (`fnE + 0xec`) and `PV` (`fnE + 0x144`) -/
abbrev mvJ : Nat := fnE + 0xec
abbrev pvJ : Nat := fnE + 0x144

/-- the prologue's frame writes: `FW` of SlowRel (saved FP/LR and the window slots) -/
@[reducible] def FWp (sp : Nat) : List (Nat × Nat) := [(sp - 8, sp + 424), (sp + 440, sp + 544)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`fnE` → `MV` (reuse) / `makeslice(1, 1)` / `makeslice(len x, len x + 4)`** -/
theorem runE {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop)
    (sp g zp zl zc st xp xl xc yp yl yc mp ml mc ret : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 544 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 8) 552 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 128)
    (hxl : xl ≤ 128) (hret48 : ret < 2 ^ 48)
    (hzp : zp < 2 ^ 64) (hzl : zl < 2 ^ 64) (hzc : zc < 2 ^ 40) (hxp : xp < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hyp : yp < 2 ^ 64) (hyl : yl < 2 ^ 64) (hyc : yc < 2 ^ 64) (hmp : mp < 2 ^ 64)
    (hml : ml < 2 ^ 64) (hmc : mc < 2 ^ 64) (hst : st < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnE) (hsp : S.sp = BitVec.ofNat 64 (sp + 432))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 ml) (h12 : S.regs 12 = BitVec.ofNat 64 mc)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (K0 : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mvJ → S'.sp = BitVec.ofNat 64 sp → xl ≤ zc →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 xl → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 xp → S'.regs 5 = BitVec.ofNat 64 xl →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FWp sp) → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = r29.toNat → M'.readLE sp 8 = ret →
      M'.readLE (sp + 464) 8 = st → M'.readLE (sp + 472) 8 = xp → M'.readLE (sp + 480) 8 = xl →
      M'.readLE (sp + 488) 8 = xc → M'.readLE (sp + 496) 8 = yp → M'.readLE (sp + 504) 8 = yl →
      M'.readLE (sp + 520) 8 = mp → M'.readLE (sp + 528) 8 = ml → M'.readLE (sp + 536) 8 = mc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K1 : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mkA → S'.sp = BitVec.ofNat 64 sp → zc < xl →
      xl = 1 → S'.regs 0 = 2641088#64 → S'.regs 1 = BitVec.ofNat 64 1 → S'.regs 2 = BitVec.ofNat 64 1 →
      S'.regs 30 = BitVec.ofNat 64 mk1R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FWp sp) → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = r29.toNat → M'.readLE sp 8 = ret →
      M'.readLE (sp + 464) 8 = st → M'.readLE (sp + 472) 8 = xp → M'.readLE (sp + 480) 8 = xl →
      M'.readLE (sp + 488) 8 = xc → M'.readLE (sp + 496) 8 = yp → M'.readLE (sp + 504) 8 = yl →
      M'.readLE (sp + 520) 8 = mp → M'.readLE (sp + 528) 8 = ml → M'.readLE (sp + 536) 8 = mc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KN : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mkA → S'.sp = BitVec.ofNat 64 sp → zc < xl →
      xl ≠ 1 → S'.regs 0 = 2641088#64 → S'.regs 1 = BitVec.ofNat 64 xl → S'.regs 2 = BitVec.ofNat 64 (xl + 4) →
      S'.regs 30 = BitVec.ofNat 64 mk2R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FWp sp) → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = r29.toNat → M'.readLE sp 8 = ret →
      M'.readLE (sp + 464) 8 = st → M'.readLE (sp + 472) 8 = xp → M'.readLE (sp + 480) 8 = xl →
      M'.readLE (sp + 488) 8 = xc → M'.readLE (sp + 496) 8 = yp → M'.readLE (sp + 504) 8 = yl →
      M'.readLE (sp + 520) 8 = mp → M'.readLE (sp + 528) 8 = ml → M'.readLE (sp + 536) 8 = mc →
      M'.readLE (sp + 112) 8 = xl + 4 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at K0 K1 KN
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 432) - 432#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus_run [es1, es2, hacc] until [mvJ, mkA]
  · refine K1 _ _ rfl ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 424)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 440, sp + 544)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
  · refine KN _ _ rfl ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 424)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 440, sp + 544)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
    all_goals (apply BitVec.eq_of_toNat_eq; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega)
  · refine K0 _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 424)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 440, sp + 544)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`mk1R` → `MV`** (return of `makeslice(1, 1)`) -/
theorem runM1 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st xp xl yp yl : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 544 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 552 true = true)
    (r464 : M.readLE (sp + 464) 8 = st) (r472 : M.readLE (sp + 472) 8 = xp) (r480 : M.readLE (sp + 480) 8 = xl)
    (r496 : M.readLE (sp + 496) 8 = yp) (r504 : M.readLE (sp + 504) 8 = yl)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mk1R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 mvJ → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = BitVec.ofNat 64 xl → S'.regs 2 = BitVec.ofNat 64 1 →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 xp → S'.regs 5 = BitVec.ofNat 64 1 →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [hal, hacc, r464, r472, r480, r496, r504] until [mvJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`mk2R` → `MV`** (return of `makeslice(len x, len x + 4)`) -/
theorem runMN {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st xp xl yp yl : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 544 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 552 true = true)
    (r464 : M.readLE (sp + 464) 8 = st) (r472 : M.readLE (sp + 472) 8 = xp) (r480 : M.readLE (sp + 480) 8 = xl)
    (r496 : M.readLE (sp + 496) 8 = yp) (r504 : M.readLE (sp + 504) 8 = yl) (r112 : M.readLE (sp + 112) 8 = xl + 4)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mk2R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 mvJ → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = BitVec.ofNat 64 xl → S'.regs 2 = BitVec.ofNat 64 (xl + 4) →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 xp → S'.regs 5 = BitVec.ofNat 64 xl →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [hal, hacc, r464, r472, r480, r496, r504, r112] until [mvJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`MV` → `PV` (same pointer) / `memmove(z, x, 8 · len x)`** -/
theorem runMV {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp z xl zc' xp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 544 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 552 true = true)
    (hz : z < 2 ^ 64) (hxl : xl < 2 ^ 40) (hzc : zc' < 2 ^ 64) (hxp : xp < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mvJ) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z) (h1 : S.regs 1 = BitVec.ofNat 64 xl) (h2 : S.regs 2 = BitVec.ofNat 64 zc')
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (KE : ∀ S' : State, S'.pc = BitVec.ofNat 64 pvJ → z = xp → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KM : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mvA → S'.sp = S.sp → z ≠ xp →
      S'.regs 0 = BitVec.ofNat 64 z → S'.regs 1 = BitVec.ofNat 64 xp → S'.regs 2 = BitVec.ofNat 64 (8 * xl) →
      S'.regs 30 = BitVec.ofNat 64 mvR →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 136, sp + 152), (sp + 344, sp + 352)] → M'.regions = M.regions →
      M'.readLE (sp + 344) 8 = z → M'.readLE (sp + 136) 8 = xl → M'.readLE (sp + 144) 8 = zc' →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KM
  generalize e28 : S.regs 28 = x28 at KM
  generalize e29 : S.regs 29 = x29 at KM
  generalize eS : S.sp = xsp at KM
  subst hmem
  janus_run [hal, hacc] until [pvJ, mvA]
  · refine KE _ rfl ?_
    exact hbr.symm
  · refine KM _ _ rfl ?_ (fun e => hbr (by rw [e])) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 136, sp + 152)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 344, sp + 352)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat]
    all_goals first | omega | skip
    all_goals first | (rw [← eS, hsp]; done) | skip
    have ea : ∀ x : BitVec 64, x &&& 18446744073709551615#64 = x := fun x => by
      rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, ea, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    rw [Janus.Contracts.Iface.lsl3_toNat, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`mvR` → `PV`** (return of `memmove`; reloads) -/
theorem runMvR {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp z xl zc' st yp yl : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 544 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 552 true = true)
    (r344 : M.readLE (sp + 344) 8 = z) (r136 : M.readLE (sp + 136) 8 = xl) (r144 : M.readLE (sp + 144) 8 = zc')
    (r464 : M.readLE (sp + 464) 8 = st) (r496 : M.readLE (sp + 496) 8 = yp) (r504 : M.readLE (sp + 504) 8 = yl)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mvR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 pvJ → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 z → S'.regs 5 = BitVec.ofNat 64 xl → S'.regs 2 = BitVec.ofNat 64 zc' →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [hal, hacc, r344, r136, r144, r464, r496, r504] until [pvJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

end FvModexp.Arm64.ExpSlow
