import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure runs of L2 (agent asm s75; twin of expmc's `SlowU2R`; nat.go:773-774)

* `runL2` (`sq2R`): `DX = [0x88]` (`v`), `BTQ $63, DX; JB` — bit clear: `SI, DI, R8 = [0xe0], [0xd8], [0x170]`
  (`zz` = the old `z`) → `fnE + 0x6b3`; bit set: spills `CX → 0xd0`, `BX → 0xc8`, `AX → 0x1a0`, `x` (`[0x208..]`)
  to `sp + 0/8/0x10`, `DI = [0x200]`, `SI, R8, R9 = AX, BX, CX`, `AX, BX, CX = [0x170], [0xe0], [0xd8]`,
  `CALL nat.mul` (return `ml2R`).
* `runL2b` (`ml2R`): `DX = [0x88]`, `SI, DI, R8 = [0xc8], [0xd0], [0x1a0]` → `fnE + 0x6b3`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- L2's stores before `nat.mul` -/
@[reducible] def wsL2 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp, sp + 0x18), (sp + 0xc8, sp + 0xd8), (sp + 0x1a0, sp + 0x1a8)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `sq2R` → `fnE + 0x6b3` (bit clear) / `nat.mul` entry (bit set) -/
theorem runL2 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp z zl zc zz zzl zzc xp xl xc st : Nat)
    (v : W64) (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (bz : z < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64)
    (bxp : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (bxc : xc < 2 ^ 64)
    (h88 : M.readLE (sp + 0x88) 8 = v.toNat) (he0 : M.readLE (sp + 0xe0) 8 = zzl)
    (hd8 : M.readLE (sp + 0xd8) 8 = zzc) (h170 : M.readLE (sp + 0x170) 8 = zz)
    (h208 : M.readLE (sp + 0x208) 8 = xp) (h210 : M.readLE (sp + 0x210) 8 = xl)
    (h218 : M.readLE (sp + 0x218) 8 = xc) (h200 : M.readLE (sp + 0x200) 8 = st)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 sq2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (KN : ∀ T : State, v.getLsbD 63 = false → T.rip = BitVec.ofNat 64 (fnE + 0x6b3) →
      T.regs 4 = BitVec.ofNat 64 sp → T.mem = M → T.regs 0 = BitVec.ofNat 64 z → T.regs 3 = BitVec.ofNat 64 zl →
      T.regs 1 = BitVec.ofNat 64 zc → T.regs 8 = BitVec.ofNat 64 zz → T.regs 6 = BitVec.ofNat 64 zzl →
      T.regs 7 = BitVec.ofNat 64 zzc → T.regs 2 = v →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 T Q)
    (KM : ∀ T : State, v.getLsbD 63 = true → T.rip = BitVec.ofNat 64 6228032 →
      T.regs 4 = BitVec.ofNat 64 (sp - 8) →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      MemFrame M T.mem (wsL2 sp) → T.mem.regions = M.regions → T.mem.readLE (sp - 8) 8 = ml2R →
      T.mem.readLE (sp + 0xd0) 8 = zc → T.mem.readLE (sp + 0x1a0) 8 = z → T.mem.readLE (sp + 0xc8) 8 = zl →
      T.mem.readLE sp 8 = xp → T.mem.readLE (sp + 8) 8 = xl → T.mem.readLE (sp + 16) 8 = xc →
      T.regs 0 = BitVec.ofNat 64 zz → T.regs 3 = BitVec.ofNat 64 zzl → T.regs 1 = BitVec.ofNat 64 zzc →
      T.regs 7 = BitVec.ofNat 64 st → T.regs 6 = BitVec.ofNat 64 z → T.regs 8 = BitVec.ofNat 64 zl →
      T.regs 9 = BitVec.ofNat 64 zc → ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have ev : BitVec.ofNat 64 v.toNat = v := by simp
  generalize x14 : S.regs 14 = r14 at KN KM
  generalize xf : S.fsBase = rf at KN KM
  generalize xx : S.xmm 15 = rx at KN KM
  generalize xd : S.df = rd at KN KM
  subst hmem
  janus64_run [e4, h88, he0, hd8, h170, h208, h210, h218, h200, ev] until [6228032, fnE + 0x6b3]
  · refine KM _ hbr rfl ?_ ?_ ?_ ?_ ?_ ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xc8, sp + 0xd8)) (by simp) (by simp only; omega)
            (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x1a0, sp + 0x1a8)) (by simp) (by simp only; omega)
            (by simp only; omega))
      exact MemFrame.refl _ _
    case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
    all_goals first | (janus64_simp; done) | exact xf | exact xx | skip
    all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | skip
  · refine KN _ (by simpa using hbr) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip
    all_goals simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals first | omega | rfl | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `ml2R` → `fnE + 0x6b3` -/
theorem runL2b {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp zl zc z : Nat)
    (v : W64) (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (h88 : M.readLE (sp + 0x88) 8 = v.toNat) (hc8 : M.readLE (sp + 0xc8) 8 = zl)
    (hd0 : M.readLE (sp + 0xd0) 8 = zc) (h1a0 : M.readLE (sp + 0x1a0) 8 = z)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 ml2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 (fnE + 0x6b3) → T.regs 4 = BitVec.ofNat 64 sp → T.mem = M →
      T.regs 0 = S.regs 0 → T.regs 3 = S.regs 3 → T.regs 1 = S.regs 1 → T.regs 8 = BitVec.ofNat 64 z →
      T.regs 6 = BitVec.ofNat 64 zl → T.regs 7 = BitVec.ofNat 64 zc → T.regs 2 = v →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have ev : BitVec.ofNat 64 v.toNat = v := by simp
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h88, hc8, hd0, h1a0, ev] until [fnE + 0x6b3]
  refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip
  all_goals simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | skip

end FvModexp.Amd64.ExpSlow
