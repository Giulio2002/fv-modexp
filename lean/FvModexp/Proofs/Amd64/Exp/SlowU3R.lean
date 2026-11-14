import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure runs of U3 (agent expmc s81)

* `runU3` (`fnE + 0x39d`): `R10 = [0x1d8]` (`len m`, `> 0`: the `len m = 0` branch is refuted), spills `AX → 0x178`,
  `BX → 0x110`, `CX → 0x108` (`z`), stack arguments `u = z` (`sp + 0/8/0x10`), `v = m` (`[0x1d0], R10, [0x1e0]` →
  `sp + 0x18/0x20/0x28`), `AX, BX, CX = R8, SI, DI` (`zz`), `DI = [0x200]`, `SI, R8, R9 = [0x160], [0x90], [0x98]`
  (`r`), `CALL nat.div` (return `dv1R`).
* `runU3b` (`dv1R`): `DX = [0x88]`, `R9, R11, R15 = CX, BX, AX` (quotient), `R12, R13 = [0x110], [0x108]`,
  `[0x160] := [0x178]` (old `z`), `AX, BX, CX = DI, SI, R8` (remainder), `R8, SI, DI = [0x168], [0xa0], [0xa8]`
  (old `q`) → `j1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- U3's stores before `nat.div` -/
@[reducible] def wsU3 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp, sp + 0x30), (sp + 0x108, sp + 0x118), (sp + 0x178, sp + 0x180)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `fnE + 0x39d` → `nat.div` entry -/
theorem runU3 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp z zl zc zz zzl zzc rr rl rc mp ml mc st : Nat)
    (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (bz : z < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64)
    (bmp : mp < 2 ^ 64) (bml : ml < 2 ^ 64) (bmc : mc < 2 ^ 64) (hml0 : 0 < ml)
    (h1d8 : M.readLE (sp + 0x1d8) 8 = ml) (h1d0 : M.readLE (sp + 0x1d0) 8 = mp)
    (h1e0 : M.readLE (sp + 0x1e0) 8 = mc) (h200 : M.readLE (sp + 0x200) 8 = st)
    (h160 : M.readLE (sp + 0x160) 8 = rr) (h90 : M.readLE (sp + 0x90) 8 = rl) (h98 : M.readLE (sp + 0x98) 8 = rc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (fnE + 0x39d)) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h8 : S.regs 8 = BitVec.ofNat 64 zz) (h6 : S.regs 6 = BitVec.ofNat 64 zzl) (h7 : S.regs 7 = BitVec.ofNat 64 zzc)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 6217504 → T.regs 4 = BitVec.ofNat 64 (sp - 8) →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      MemFrame M T.mem (wsU3 sp) → T.mem.regions = M.regions → T.mem.readLE (sp - 8) 8 = dv1R →
      T.mem.readLE (sp + 0x178) 8 = z → T.mem.readLE (sp + 0x110) 8 = zl → T.mem.readLE (sp + 0x108) 8 = zc →
      T.mem.readLE sp 8 = z → T.mem.readLE (sp + 8) 8 = zl → T.mem.readLE (sp + 16) 8 = zc →
      T.mem.readLE (sp + 24) 8 = mp → T.mem.readLE (sp + 32) 8 = ml → T.mem.readLE (sp + 40) 8 = mc →
      T.regs 0 = BitVec.ofNat 64 zz → T.regs 3 = BitVec.ofNat 64 zzl → T.regs 1 = BitVec.ofNat 64 zzc →
      T.regs 7 = BitVec.ofNat 64 st → T.regs 6 = BitVec.ofNat 64 rr → T.regs 8 = BitVec.ofNat 64 rl →
      T.regs 9 = BitVec.ofNat 64 rc → ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [e4, h1d8, h1d0, h1e0, h200, h160, h90, h98] until [6217504, j1]
  refine K _ rfl ?g4 ?g14 ?gfs ?gx ?gdf ?mf ?rg ?ra ?m178 ?m110 ?m108 ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?r0 ?r3 ?r1 ?r7 ?r6 ?r8 ?r9
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp, sp + 0x30)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x108, sp + 0x118)) (by simp) (by simp only; omega)
          (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x178, sp + 0x180)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case gfs => exact xf
  case gx => exact xx
  case g4 => janus64_simp
  case g14 => janus64_simp
  case gdf => janus64_simp
  case r0 => janus64_simp
  case r3 => janus64_simp
  case r1 => janus64_simp
  case r7 => janus64_simp
  case r6 => janus64_simp
  case r8 => janus64_simp
  case r9 => janus64_simp
  case ra => janus64_simp
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `dv1R` → `j1` -/
theorem runU3b {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp zl zc z q ql qc : Nat) (v : W64)
    (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (bz : z < 2 ^ 64)
    (h88 : M.readLE (sp + 0x88) 8 = v.toNat) (h110 : M.readLE (sp + 0x110) 8 = zl)
    (h108 : M.readLE (sp + 0x108) 8 = zc) (h178 : M.readLE (sp + 0x178) 8 = z)
    (h168 : M.readLE (sp + 0x168) 8 = q) (ha0 : M.readLE (sp + 0xa0) 8 = ql) (ha8 : M.readLE (sp + 0xa8) 8 = qc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 dv1R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 j1 → T.regs 4 = BitVec.ofNat 64 sp →
      MemFrame M T.mem [(sp + 0x160, sp + 0x168)] → T.mem.regions = M.regions → T.mem.readLE (sp + 0x160) 8 = z →
      T.regs 0 = S.regs 7 → T.regs 3 = S.regs 6 → T.regs 1 = S.regs 8 →
      T.regs 15 = S.regs 0 → T.regs 11 = S.regs 3 → T.regs 9 = S.regs 1 →
      T.regs 8 = BitVec.ofNat 64 q → T.regs 6 = BitVec.ofNat 64 ql → T.regs 7 = BitVec.ofNat 64 qc →
      T.regs 12 = BitVec.ofNat 64 zl → T.regs 13 = BitVec.ofNat 64 zc → T.regs 2 = v →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have ev : BitVec.ofNat 64 v.toNat = v := by simp
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x7 : S.regs 7 = r7 at K
  generalize x6 : S.regs 6 = r6 at K
  generalize x8 : S.regs 8 = r8 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h88, h110, h108, h178, h168, ha0, ha8, ev] until [j1]
  refine K _ rfl ?g4 ?mf ?rg ?m160 ?r0 ?r3 ?r1 ?r15 ?r11 ?r9 ?r8 ?r6 ?r7 ?r12 ?r13 ?r2 ?g14 ?gfs ?gx ?gdf
  case mf =>
    refine MemFrame.writeLE ?_ _ (r := (sp + 0x160, sp + 0x168)) (by simp) (by simp only; omega)
      (by simp only; omega)
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case gfs => exact xf
  case gx => exact xx
  case m160 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]; omega
  all_goals janus64_simp

end FvModexp.Amd64.ExpSlow
