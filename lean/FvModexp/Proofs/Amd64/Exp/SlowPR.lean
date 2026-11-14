import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure runs of the prologue and `z = z.set(x)` (agent expmc s79; twin of arm64
`SlowPR`, mechanics of asm's amd64 `EvSetR`)

nat.go:732-733, 58-69, 93-94 (inlined `z.make(len x)` + `copy(z, x)`):
* `runE`: `fnE` → stack guard, `PUSHQ BP`, `SUBQ $0x1a8`, spills `AX → 0x1e8, DI → 0x200, R9 → 0x218, R8 → 0x210,
  SI → 0x208`; `len x ≤ cap z` (signed `JL`) → reuse (`DX = len x`, to `setJ`), else `makeslice(Word, 1, 1)`
  (`len x = 1`) or `makeslice(Word, len x, len x + 4)` (`len x + 4` spilled to `0x68`);
* `runM1` / `runMN`: the two `makeslice` returns → `setJ` (reloads `DX, SI, DI, R9`; `R8 = len`, `CX = cap`);
* `runJ`: `setJ` (`R10 = R8 = len x`; `CMOVL` min) → same pointer → `aSet`; else spills `CX → 0x80, R10 → 0x138,
  AX → 0x158` and `memmove(z, x, 8·len x)`; `runMv`: `mvR` → `aSet` (reloads).
Only the listed registers are carried over; memory changes are framed.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow


/-- the prologue's writes (saved `BP` and spills, `len x + 4` at `0x68`, the call's return address at `sp - 8`) -/
@[reducible] def FWp (sp : Nat) : List (Nat × Nat) := [(sp - 8, sp + 0x1b0), (sp + 0x1e8, sp + 0x220)]

/-- `runJ`'s writes before `memmove` -/
@[reducible] def FM (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x80, sp + 0x88), (sp + 0x138, sp + 0x140), (sp + 0x158, sp + 0x160)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `fnE` → `setJ` (reuse) / `makeslice` (two sizes) -/
theorem runE {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp g zp zc st xp xl xc bp : Nat)
    (M : Memory) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 0x228 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 0x80)
    (hbp : bp < 2 ^ 64) (hzp : zp < 2 ^ 64) (hzc : zc < 2 ^ 40) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 40)
    (hxc : xc < 2 ^ 64) (hst : st < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnE) (h4 : S.regs 4 = BitVec.ofNat 64 (sp + 0x1b0))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zc) (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h5 : S.regs 5 = BitVec.ofNat 64 bp) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (K0 : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 setJ → S'.regs 4 = BitVec.ofNat 64 sp → xl ≤ zc →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 zc → S'.regs 2 = BitVec.ofNat 64 xl →
      S'.regs 8 = BitVec.ofNat 64 xl → S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 7 = BitVec.ofNat 64 st →
      S'.regs 9 = BitVec.ofNat 64 xc →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = M' →
      MemFrame M M' (FWp sp) → M'.regions = M.regions →
      M'.readLE (sp + 0x1a8) 8 = bp → M'.readLE (sp + 0x1e8) 8 = zp → M'.readLE (sp + 0x200) 8 = st →
      M'.readLE (sp + 0x208) 8 = xp → M'.readLE (sp + 0x210) 8 = xl → M'.readLE (sp + 0x218) 8 = xc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K1 : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mkE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      zc < xl → xl = 1 →
      S'.regs 0 = BitVec.ofNat 64 7233184 → S'.regs 3 = BitVec.ofNat 64 1 → S'.regs 1 = BitVec.ofNat 64 1 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = M' →
      MemFrame M M' (FWp sp) → M'.regions = M.regions → M'.readLE (sp - 8) 8 = mk1R →
      M'.readLE (sp + 0x1a8) 8 = bp → M'.readLE (sp + 0x1e8) 8 = zp → M'.readLE (sp + 0x200) 8 = st →
      M'.readLE (sp + 0x208) 8 = xp → M'.readLE (sp + 0x210) 8 = xl → M'.readLE (sp + 0x218) 8 = xc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mkE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      zc < xl → xl ≠ 1 →
      S'.regs 0 = BitVec.ofNat 64 7233184 → S'.regs 3 = BitVec.ofNat 64 xl → S'.regs 1 = BitVec.ofNat 64 (xl + 4) →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = M' →
      MemFrame M M' (FWp sp) → M'.regions = M.regions → M'.readLE (sp - 8) 8 = mk2R →
      M'.readLE (sp + 0x1a8) 8 = bp → M'.readLE (sp + 0x1e8) 8 = zp → M'.readLE (sp + 0x200) 8 = st →
      M'.readLE (sp + 0x208) 8 = xp → M'.readLE (sp + 0x210) 8 = xl → M'.readLE (sp + 0x218) 8 = xc →
      M'.readLE (sp + 0x68) 8 = xl + 4 →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 0x1b0) - 8#64 = BitVec.ofNat 64 (sp + 0x1a8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 0x1a8) - 0x1a8#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize xf : S.fsBase = rf at K0 K1 KN
  generalize xx : S.xmm 15 = rx at K0 K1 KN
  generalize xd : S.df = rd at K0 K1 KN
  subst hmem
  janus64_run [es1, es2, es3] until [setJ, mkE]
  · refine K1 _ _ rfl ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x1b0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x1e8, sp + 0x220)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip
  · refine KN _ _ rfl ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x1b0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x1e8, sp + 0x220)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip
    apply BitVec.eq_of_toNat_eq; simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega
  · refine K0 _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x1b0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x1e8, sp + 0x220)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mk1R` (return of `makeslice(Word, 1, 1)`) → `setJ` -/
theorem runM1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st xp xl xc : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (h200 : M.readLE (sp + 0x200) 8 = st) (h208 : M.readLE (sp + 0x208) 8 = xp) (h210 : M.readLE (sp + 0x210) 8 = xl)
    (h218 : M.readLE (sp + 0x218) 8 = xc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mk1R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 setJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = BitVec.ofNat 64 1 → S'.regs 2 = BitVec.ofNat 64 xl →
      S'.regs 8 = BitVec.ofNat 64 1 → S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 7 = BitVec.ofNat 64 st →
      S'.regs 9 = BitVec.ofNat 64 xc →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize x0 : S.regs 0 = r0 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h200, h208, h210, h218] until [setJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mk2R` (return of `makeslice(Word, len x, len x + 4)`) → `setJ` -/
theorem runMN {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st xp xl xc : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (h200 : M.readLE (sp + 0x200) 8 = st) (h208 : M.readLE (sp + 0x208) 8 = xp) (h210 : M.readLE (sp + 0x210) 8 = xl)
    (h218 : M.readLE (sp + 0x218) 8 = xc) (h68 : M.readLE (sp + 0x68) 8 = xl + 4)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mk2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 setJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = BitVec.ofNat 64 (xl + 4) → S'.regs 2 = BitVec.ofNat 64 xl →
      S'.regs 8 = BitVec.ofNat 64 xl → S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 7 = BitVec.ofNat 64 st →
      S'.regs 9 = BitVec.ofNat 64 xc →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize x0 : S.regs 0 = r0 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h200, h208, h210, h218, h68] until [setJ]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `setJ` → `aSet` (same pointer) / `memmove(z, x, 8·len x)` -/
theorem runJ {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st xp xl xc pZ cZ : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (hxp : xp < 2 ^ 64) (hl : xl < 2 ^ 40) (hpZ : pZ < 2 ^ 64) (hcZ : cZ < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 setJ) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pZ) (h1 : S.regs 1 = BitVec.ofNat 64 cZ) (h2 : S.regs 2 = BitVec.ofNat 64 xl)
    (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h6 : S.regs 6 = BitVec.ofNat 64 xp)
    (KE : ∀ S' : State, S'.rip = BitVec.ofNat 64 aSet → S'.regs 4 = BitVec.ofNat 64 sp → pZ = xp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 1 = BitVec.ofNat 64 cZ → S'.regs 2 = BitVec.ofNat 64 xl →
      S'.regs 10 = BitVec.ofNat 64 xl → S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 7 = S.regs 7 →
      S'.regs 9 = S.regs 9 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KM : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 mvE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      pZ ≠ xp → S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 3 = BitVec.ofNat 64 xp →
      S'.regs 1 = BitVec.ofNat 64 (8 * xl) →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = M' →
      MemFrame M M' (FM sp) → M'.regions = M.regions → M'.readLE (sp - 8) 8 = mvR →
      M'.readLE (sp + 0x80) 8 = cZ → M'.readLE (sp + 0x138) 8 = xl → M'.readLE (sp + 0x158) 8 = pZ →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x7 : S.regs 7 = r7 at KE KM
  generalize x9 : S.regs 9 = r9 at KE KM
  generalize x14 : S.regs 14 = r14 at KE KM
  generalize xf : S.fsBase = rf at KE KM
  generalize xx : S.xmm 15 = rx at KE KM
  generalize xd : S.df = rd at KE KM
  subst hmem
  janus64_run [e4] until [aSet, mvE]
  · refine KE _ rfl ?_ (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip
    all_goals simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip
  · refine KM _ _ rfl ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x80, sp + 0x88)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x138, sp + 0x140)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x158, sp + 0x160)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | exact xf | exact xx | skip
    apply BitVec.eq_of_toNat_eq; simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat]; rw [Nat.shiftLeft_eq]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mvR` (return of `memmove`) → `aSet` -/
theorem runMv {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st xp xl xc pZ cZ : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (h200 : M.readLE (sp + 0x200) 8 = st) (h208 : M.readLE (sp + 0x208) 8 = xp) (h210 : M.readLE (sp + 0x210) 8 = xl)
    (h218 : M.readLE (sp + 0x218) 8 = xc) (h80 : M.readLE (sp + 0x80) 8 = cZ) (h138 : M.readLE (sp + 0x138) 8 = xl)
    (h158 : M.readLE (sp + 0x158) 8 = pZ)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mvR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 aSet → S'.regs 4 = BitVec.ofNat 64 sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 1 = BitVec.ofNat 64 cZ → S'.regs 2 = BitVec.ofNat 64 xl →
      S'.regs 10 = BitVec.ofNat 64 xl → S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 7 = BitVec.ofNat 64 st →
      S'.regs 9 = BitVec.ofNat 64 xc →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h200, h208, h210, h218, h80, h138, h158] until [aSet]
  refine K _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip

end FvModexp.Amd64.ExpSlow
