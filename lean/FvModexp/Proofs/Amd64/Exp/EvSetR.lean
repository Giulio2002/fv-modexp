import FvModexp.Proofs.Amd64.Exp.EvMv

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the pure runs of `z = z.set(z2)` (asm s61; twin of infra's arm64 `EvSetR`)

nat.go:58-69, 93-94 (inlined `z.make(len z2)` + `copy(z, z2)`): `runS` (`exp2R`: spill `z2` (`RAX/RBX/RCX`) to
`0xf8/0x80/0x88`; `len z2 ≤ cap z` (signed `JG`) → reuse `z` (to `setJ`), else `makeslice(Word, 1, 1)` (`len z2 = 1`) or
`makeslice(Word, len, len + 4)` (`len + 4` spilled to `0x78`)), `runM1` / `runMN` (the two `makeslice` returns →
`setJ`), `runJ` (`setJ`: spill `z` to `0x108/0xa0/0xa8`; `CMOVL` min (= `len z2`); same pointer → `mvJ`, else
`memmove(z, z2, 8·len)`), `runMv` (`mvR` → `mvJ`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `exp2R` → `setJ` (reuse) / `makeslice` (two sizes) -/
theorem runS {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp zp zc pw lw cw : Nat) (M : Memory)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h80 : M.readLE (sp + 0x180) 8 = zp) (h90 : M.readLE (sp + 0x190) 8 = zc) (hzc : zc < 2 ^ 40)
    (hp : pw < 2 ^ 64) (hl : lw < 2 ^ 40) (hc : cw < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 exp2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h3 : S.regs 3 = BitVec.ofNat 64 lw) (h1 : S.regs 1 = BitVec.ofNat 64 cw)
    (K0 : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 setJ → S'.regs 4 = BitVec.ofNat 64 sp → lw ≤ zc →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 cw → S'.regs 3 = BitVec.ofNat 64 lw →
      S'.regs 6 = BitVec.ofNat 64 lw → S'.regs 7 = BitVec.ofNat 64 zp → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = M' →
      MemFrame M M' [(sp + 0x80, sp + 0x90), (sp + 0xf8, sp + 0x100)] → M'.regions = M.regions →
      M'.readLE (sp + 0xf8) 8 = pw → M'.readLE (sp + 0x80) 8 = lw → M'.readLE (sp + 0x88) 8 = cw →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (K1 : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mkE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      zc < lw → lw = 1 →
      S'.regs 0 = BitVec.ofNat 64 7233184 → S'.regs 3 = BitVec.ofNat 64 1 → S'.regs 1 = BitVec.ofNat 64 1 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = M' →
      MemFrame M M' [(sp - 8, sp), (sp + 0x80, sp + 0x90), (sp + 0xf8, sp + 0x100)] → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = mk1R →
      M'.readLE (sp + 0xf8) 8 = pw → M'.readLE (sp + 0x80) 8 = lw → M'.readLE (sp + 0x88) 8 = cw →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mkE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      zc < lw → lw ≠ 1 →
      S'.regs 0 = BitVec.ofNat 64 7233184 → S'.regs 3 = BitVec.ofNat 64 lw → S'.regs 1 = BitVec.ofNat 64 (lw + 4) →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = M' →
      MemFrame M M' [(sp - 8, sp), (sp + 0x78, sp + 0x90), (sp + 0xf8, sp + 0x100)] → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = mkNR →
      M'.readLE (sp + 0xf8) 8 = pw → M'.readLE (sp + 0x80) 8 = lw → M'.readLE (sp + 0x88) 8 = cw →
      M'.readLE (sp + 0x78) 8 = lw + 4 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x5 : S.regs 5 = r5 at K0 K1 KN
  generalize x14 : S.regs 14 = r14 at K0 K1 KN
  generalize xf : S.fsBase = rf at K0 K1 KN
  generalize xx : S.xmm 15 = rx at K0 K1 KN
  generalize xd : S.df = rd at K0 K1 KN
  janus64_run [h80, h90, e4] until [setJ, mkE]
  · refine K1 _ _ rfl ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x80, sp + 0x90)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xf8, sp + 0x100)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip
  · refine KN _ _ rfl ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x78, sp + 0x90)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xf8, sp + 0x100)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip
    apply BitVec.eq_of_toNat_eq; simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega
  · refine K0 _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x80, sp + 0x90)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xf8, sp + 0x100)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mk1R` (return of `makeslice(Word, 1, 1)`) → `setJ` -/
theorem runM1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp pw lw cw : Nat) (M : Memory)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hf8 : M.readLE (sp + 0xf8) 8 = pw) (h80 : M.readLE (sp + 0x80) 8 = lw) (h88 : M.readLE (sp + 0x88) 8 = cw)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mk1R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 setJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 cw → S'.regs 3 = BitVec.ofNat 64 1 →
      S'.regs 6 = BitVec.ofNat 64 lw → S'.regs 7 = S.regs 0 → S'.regs 2 = BitVec.ofNat 64 1 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize x0 : S.regs 0 = r0 at K
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hf8, h80, h88] until [setJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mkNR` (return of `makeslice(Word, len, len + 4)`) → `setJ` -/
theorem runMN {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp pw lw cw : Nat) (M : Memory)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hf8 : M.readLE (sp + 0xf8) 8 = pw) (h80 : M.readLE (sp + 0x80) 8 = lw) (h88 : M.readLE (sp + 0x88) 8 = cw)
    (h78 : M.readLE (sp + 0x78) 8 = lw + 4)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mkNR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 setJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 cw → S'.regs 3 = BitVec.ofNat 64 lw →
      S'.regs 6 = BitVec.ofNat 64 lw → S'.regs 7 = S.regs 0 → S'.regs 2 = BitVec.ofNat 64 (lw + 4) →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize x0 : S.regs 0 = r0 at K
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hf8, h80, h88, h78] until [setJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `setJ` → `mvJ` (same pointer) / `memmove(z, z2, 8·len)` -/
theorem runJ {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp pw lw cw pZ cZ : Nat) (M : Memory)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hpw : pw < 2 ^ 64) (hl : lw < 2 ^ 40) (hpZ : pZ < 2 ^ 64) (hcZ : cZ < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 setJ) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h3 : S.regs 3 = BitVec.ofNat 64 lw) (h2 : S.regs 2 = BitVec.ofNat 64 cZ)
    (h6 : S.regs 6 = BitVec.ofNat 64 lw) (h7 : S.regs 7 = BitVec.ofNat 64 pZ) (h1 : S.regs 1 = BitVec.ofNat 64 cw)
    (KE : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mvJ → S'.regs 4 = BitVec.ofNat 64 sp → pZ = pw →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 cw → S'.regs 6 = BitVec.ofNat 64 lw →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = M' →
      MemFrame M M' [(sp + 0xa0, sp + 0xb0), (sp + 0x108, sp + 0x110)] → M'.regions = M.regions →
      M'.readLE (sp + 0x108) 8 = pZ → M'.readLE (sp + 0xa0) 8 = lw → M'.readLE (sp + 0xa8) 8 = cZ →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (KM : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mvE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) → pZ ≠ pw →
      S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 3 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 (8 * lw) →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = M' →
      MemFrame M M' [(sp - 8, sp), (sp + 0xa0, sp + 0xb0), (sp + 0x108, sp + 0x110)] → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = mvR →
      M'.readLE (sp + 0x108) 8 = pZ → M'.readLE (sp + 0xa0) 8 = lw → M'.readLE (sp + 0xa8) 8 = cZ →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x5 : S.regs 5 = r5 at KE KM
  generalize x14 : S.regs 14 = r14 at KE KM
  generalize xf : S.fsBase = rf at KE KM
  generalize xx : S.xmm 15 = rx at KE KM
  generalize xd : S.df = rd at KE KM
  janus64_run [e4] until [mvJ, mvE]
  · refine KE _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa0, sp + 0xb0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x108, sp + 0x110)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | (janus64_simp; first | exact h0 | exact h1 | exact h6) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | exact xf | exact xx | skip
  · refine KM _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa0, sp + 0xb0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x108, sp + 0x110)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | (janus64_simp; first | exact h0 | exact h1 | exact h6) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | exact xf | exact xx | skip
    apply BitVec.eq_of_toNat_eq; simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat]; rw [Nat.shiftLeft_eq]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mvR` (return of `memmove`) → `mvJ` -/
theorem runMv {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp pw lw cw : Nat) (M : Memory)
    (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hf8 : M.readLE (sp + 0xf8) 8 = pw) (h80 : M.readLE (sp + 0x80) 8 = lw) (h88 : M.readLE (sp + 0x88) 8 = cw)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mvR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 mvJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 cw → S'.regs 6 = BitVec.ofNat 64 lw →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hf8, h80, h88] until [mvJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip

end FvModexp.Amd64.ExpEven
