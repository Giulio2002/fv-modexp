import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure runs of L3 (agent asm s75; nat.go:778-780)

* `runL3` (`fnE + 0x6b3`): `R10 = [0x1d8]` (`len m > 0`: `JNE` taken), spills `AX → 0x198`, `BX → 0x148`,
  `CX → 0x140`, `u = z` and `v = m` to `sp + 0..0x28`, `AX, BX, CX = R8, SI, DI` (`zz`), `DI = [0x200]`,
  `SI, R8, R9 = [0x160], [0xf0], [0xe8]` (`r`), `CALL nat.div` (return `dv2R`).
* `runL3b` (`dv2R`): `DX = [0x88]`, `R10 = [0x1d8]`, `(R15, R9, R11) = (AX, BX, CX)` (quotient),
  `R12, R13 = [0x148], [0x140]`, `(AX, BX, CX) = (DI, SI, R8)` (remainder), `[0x160] = [0x198]` (old `z`),
  `R8, SI, DI = [0x168], [0x100], [0xf8]` (old `q`), `JMP j2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- L3's stores before `nat.div` -/
@[reducible] def wsL3 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp + 0x30), (sp + 0x140, sp + 0x150), (sp + 0x198, sp + 0x1a0)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `fnE + 0x6b3` → `nat.div` entry -/
theorem runL3 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp z zl zc zz zzl zzc rr rl rc mp ml mc st : Nat)
    (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (bz : z < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64)
    (bzz : zz < 2 ^ 64) (bzzl : zzl < 2 ^ 64) (bzzc : zzc < 2 ^ 64) (hml0 : 0 < ml) (hml : ml < 2 ^ 64)
    (bmp : mp < 2 ^ 64) (bmc : mc < 2 ^ 64)
    (h1d8 : M.readLE (sp + 0x1d8) 8 = ml) (h1d0 : M.readLE (sp + 0x1d0) 8 = mp)
    (h1e0 : M.readLE (sp + 0x1e0) 8 = mc) (h200 : M.readLE (sp + 0x200) 8 = st)
    (h160 : M.readLE (sp + 0x160) 8 = rr) (hf0 : M.readLE (sp + 0xf0) 8 = rl) (he8 : M.readLE (sp + 0xe8) 8 = rc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (fnE + 0x6b3)) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h8 : S.regs 8 = BitVec.ofNat 64 zz) (h6 : S.regs 6 = BitVec.ofNat 64 zzl) (h7 : S.regs 7 = BitVec.ofNat 64 zzc)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 6217504 → T.regs 4 = BitVec.ofNat 64 (sp - 8) →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      MemFrame M T.mem (wsL3 sp) → T.mem.regions = M.regions → T.mem.readLE (sp - 8) 8 = dv2R →
      T.mem.readLE (sp + 0x198) 8 = z → T.mem.readLE (sp + 0x148) 8 = zl → T.mem.readLE (sp + 0x140) 8 = zc →
      T.mem.readLE sp 8 = z → T.mem.readLE (sp + 8) 8 = zl → T.mem.readLE (sp + 16) 8 = zc →
      T.mem.readLE (sp + 24) 8 = mp → T.mem.readLE (sp + 32) 8 = ml → T.mem.readLE (sp + 40) 8 = mc →
      T.regs 0 = BitVec.ofNat 64 zz → T.regs 3 = BitVec.ofNat 64 zzl → T.regs 1 = BitVec.ofNat 64 zzc →
      T.regs 7 = BitVec.ofNat 64 st → T.regs 6 = BitVec.ofNat 64 rr → T.regs 8 = BitVec.ofNat 64 rl →
      T.regs 9 = BitVec.ofNat 64 rc → ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hne : BitVec.ofNat 64 ml ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [e4, h1d8, h1d0, h1e0, h200, h160, hf0, he8, hne] until [6217504]
  refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x30)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x140, sp + 0x150)) (by simp) (by simp only; omega)
          (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x198, sp + 0x1a0)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals first | (janus64_simp; done) | exact xf | exact xx | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `dv2R` → `j2` -/
theorem runL3b {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp z zl zc q ql qc : Nat)
    (v : W64) (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (bz : z < 2 ^ 64)
    (h88 : M.readLE (sp + 0x88) 8 = v.toNat) (h198 : M.readLE (sp + 0x198) 8 = z)
    (h148 : M.readLE (sp + 0x148) 8 = zl) (h140 : M.readLE (sp + 0x140) 8 = zc)
    (h168 : M.readLE (sp + 0x168) 8 = q) (h100 : M.readLE (sp + 0x100) 8 = ql) (hf8 : M.readLE (sp + 0xf8) 8 = qc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 dv2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 j2 → T.regs 4 = BitVec.ofNat 64 sp →
      MemFrame M T.mem [(sp + 0x160, sp + 0x168)] → T.mem.regions = M.regions →
      T.mem.readLE (sp + 0x160) 8 = z →
      T.regs 0 = S.regs 7 → T.regs 3 = S.regs 6 → T.regs 1 = S.regs 8 →
      T.regs 15 = S.regs 0 → T.regs 9 = S.regs 3 → T.regs 11 = S.regs 1 →
      T.regs 12 = BitVec.ofNat 64 zl → T.regs 13 = BitVec.ofNat 64 zc →
      T.regs 8 = BitVec.ofNat 64 q → T.regs 6 = BitVec.ofNat 64 ql → T.regs 7 = BitVec.ofNat 64 qc →
      T.regs 2 = v → T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
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
  janus64_run [h88, h198, h148, h140, h168, h100, hf8, ev] until [j2]
  refine K _ rfl ?_ ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    refine MemFrame.writeLE ?_ _ (r := (sp + 0x160, sp + 0x168)) (by simp) (by simp only; omega) (by simp only; omega)
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals first | (janus64_simp; done) | exact xf | exact xx | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

end FvModexp.Amd64.ExpSlow
