import FvModexp.Proofs.Arm64.Exp.EvLZ

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the pure runs of `z = z.set(z2)` (agent infra)

nat.go:58-69, 93-94 (inlined `z.make(len z2)` + `copy(z, z2)`): `runS` (`exp2R`: spill `z2` to `256/136/144`; `len z2 ≤
cap z` → reuse `z` (to `setJ`), else `makeslice(1, 1)` (`len z2 = 1`) or `makeslice(len, len + 4)`), `runM1` / `runMN`
(the two `makeslice` returns → `setJ`), `runJ` (`setJ`: spill `z` to `272/168/176`; same pointer → `mvR`, else
`memmove(z, z2, 8·len)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `exp2R` → `setJ` (reuse) / `makeslice` (two sizes) -/
theorem runS {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp zp zc pw lw cw : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 true = true)
    (h344 : M.readLE (sp + 344) 8 = zp) (h360 : M.readLE (sp + 360) 8 = zc) (hzc : zc < 2 ^ 40)
    (hp : pw < 2 ^ 64) (hl : lw < 2 ^ 40) (hc : cw < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 exp2R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h1 : S.regs 1 = BitVec.ofNat 64 lw) (h2 : S.regs 2 = BitVec.ofNat 64 cw)
    (K0 : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 setJ → S'.sp = S.sp → lw ≤ zc →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 lw → S'.regs 3 = BitVec.ofNat 64 zc →
      S'.regs 4 = BitVec.ofNat 64 lw → S'.regs 5 = BitVec.ofNat 64 zp → S'.regs 2 = BitVec.ofNat 64 cw →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 136, sp + 152), (sp + 256, sp + 264)] → M'.regions = M.regions →
      M'.readLE (sp + 256) 8 = pw → M'.readLE (sp + 136) 8 = lw → M'.readLE (sp + 144) 8 = cw →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (K1 : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 587344 → S'.sp = S.sp → zc < lw → lw = 1 →
      S'.regs 0 = 2641088#64 → S'.regs 1 = BitVec.ofNat 64 1 → S'.regs 2 = BitVec.ofNat 64 1 →
      S'.regs 30 = BitVec.ofNat 64 mk1R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 136, sp + 152), (sp + 256, sp + 264)] → M'.regions = M.regions →
      M'.readLE (sp + 256) 8 = pw → M'.readLE (sp + 136) 8 = lw → M'.readLE (sp + 144) 8 = cw →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (KN : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 587344 → S'.sp = S.sp → zc < lw → lw ≠ 1 →
      S'.regs 0 = 2641088#64 → S'.regs 1 = BitVec.ofNat 64 lw → S'.regs 2 = BitVec.ofNat 64 (lw + 4) →
      S'.regs 30 = BitVec.ofNat 64 mkNR →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 128, sp + 152), (sp + 256, sp + 264)] → M'.regions = M.regions →
      M'.readLE (sp + 256) 8 = pw → M'.readLE (sp + 136) 8 = lw → M'.readLE (sp + 144) 8 = cw →
      M'.readLE (sp + 128) 8 = lw + 4 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at K0 K1 KN
  generalize e28 : S.regs 28 = x28 at K0 K1 KN
  generalize e29 : S.regs 29 = x29 at K0 K1 KN
  generalize eS : S.sp = xsp at K0 K1 KN
  subst hmem
  janus_run [hal, hacc, h344, h360] until [setJ, 587344]
  · refine K1 _ _ rfl ?_ (by omega) hbr ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 136, sp + 152)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 264)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
    all_goals first | (rw [← eS, hsp]; done) | skip
  · refine KN _ _ rfl ?_ (by omega) hbr ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 128, sp + 152)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 264)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
    all_goals first | (rw [← eS, hsp]; done) | skip
    apply BitVec.eq_of_toNat_eq; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega
  · refine K0 _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 136, sp + 152)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 264)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
    all_goals first | (rw [← eS, hsp]; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mk1R` (return of `makeslice(1, 1)`) → `setJ` -/
theorem runM1 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp pw lw cw : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 true = true)
    (h256 : M.readLE (sp + 256) 8 = pw) (h136 : M.readLE (sp + 136) 8 = lw) (h144 : M.readLE (sp + 144) 8 = cw)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mk1R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 setJ → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 1 → S'.regs 3 = BitVec.ofNat 64 1 →
      S'.regs 4 = BitVec.ofNat 64 lw → S'.regs 5 = S.regs 0 → S'.regs 2 = BitVec.ofNat 64 cw →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [hal, hacc, h256, h136, h144] until [setJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mkNR` (return of `makeslice(len, len + 4)`) → `setJ` -/
theorem runMN {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp pw lw cw : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 true = true)
    (h256 : M.readLE (sp + 256) 8 = pw) (h136 : M.readLE (sp + 136) 8 = lw) (h144 : M.readLE (sp + 144) 8 = cw)
    (h128 : M.readLE (sp + 128) 8 = lw + 4)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mkNR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 setJ → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 lw → S'.regs 3 = BitVec.ofNat 64 (lw + 4) →
      S'.regs 4 = BitVec.ofNat 64 lw → S'.regs 5 = S.regs 0 → S'.regs 2 = BitVec.ofNat 64 cw →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [hal, hacc, h256, h136, h144, h128] until [setJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `setJ` → `mvR` (same pointer) / `memmove(z, z2, 8·len)` -/
theorem runJ {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp pw lw cw pZ cZ : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 true = true)
    (hpw : pw < 2 ^ 64) (hl : lw < 2 ^ 40) (hpZ : pZ < 2 ^ 64) (hcZ : cZ < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 setJ) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h1 : S.regs 1 = BitVec.ofNat 64 lw) (h3 : S.regs 3 = BitVec.ofNat 64 cZ)
    (h4 : S.regs 4 = BitVec.ofNat 64 lw) (h5 : S.regs 5 = BitVec.ofNat 64 pZ) (h2 : S.regs 2 = BitVec.ofNat 64 cw)
    (KE : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mvJ → S'.sp = S.sp → pZ = pw →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 2 = BitVec.ofNat 64 cw →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 168, sp + 184), (sp + 272, sp + 280)] → M'.regions = M.regions →
      M'.readLE (sp + 272) 8 = pZ → M'.readLE (sp + 168) 8 = lw → M'.readLE (sp + 176) 8 = cZ →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (KM : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mvE → S'.sp = S.sp → pZ ≠ pw →
      S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 1 = BitVec.ofNat 64 pw → S'.regs 2 = BitVec.ofNat 64 (8 * lw) →
      S'.regs 30 = BitVec.ofNat 64 mvR →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 168, sp + 184), (sp + 272, sp + 280)] → M'.regions = M.regions →
      M'.readLE (sp + 272) 8 = pZ → M'.readLE (sp + 168) 8 = lw → M'.readLE (sp + 176) 8 = cZ →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KE KM
  generalize e28 : S.regs 28 = x28 at KE KM
  generalize e29 : S.regs 29 = x29 at KE KM
  generalize eS : S.sp = xsp at KE KM
  subst hmem
  janus_run [hal, hacc] until [mvJ, mvE]
  · refine KE _ _ rfl ?_ hbr.symm ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 168, sp + 184)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 272, sp + 280)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat]
    all_goals first | omega | skip
    all_goals first | (rw [← eS, hsp]; done) | skip
  · refine KM _ _ rfl ?_ (fun e => hbr e.symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 168, sp + 184)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 272, sp + 280)) (by simp) (by simp only; omega) (by simp only; omega))
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
/-- the run `mvR` (return of `memmove`) → `mvJ` -/
theorem runMv {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp pw cw : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 true = true)
    (h256 : M.readLE (sp + 256) 8 = pw) (h144 : M.readLE (sp + 144) 8 = cw)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mvR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 mvJ → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 2 = BitVec.ofNat 64 cw →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [hal, hacc, h256, h144] until [mvJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

end FvModexp.Arm64.ExpEven
