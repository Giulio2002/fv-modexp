import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure run of the upper join (agent expmc s81)

`j1` (`fnE + 0x1f9`): `ADDQ DX, DX` (`v <<= 1`), `R10 = [0xb8] + 1` (`j + 1`), spills `R9 → 0xa8`, `R11 → 0xa0`,
`R12 → 0x90`, `R15 → 0x168` (`q`, `len r`), `DI → 0x78`, `SI → 0x70`, `R8 → 0x150` (`zz`), reloads
`SI, DI, R9, R11, R12, R15 = xp, st, xc, yl, yp, w`, `R8 = CX`, `CX = j + 1`, `R10 = BX`, `R13 = v'`, `DX = R13`
(cap r), `BX = xl` → `t1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the join's stores -/
@[reducible] def wsJ1 (sp : Nat) : List (Nat × Nat) :=
  [(sp + 0x70, sp + 0x80), (sp + 0x90, sp + 0x98), (sp + 0xa0, sp + 0xb0), (sp + 0x150, sp + 0x158),
    (sp + 0x168, sp + 0x170)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `j1` → `t1` -/
theorem runJ1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp j xp st xc yl yp w xl zz zzl zzc q ql qc rl : Nat) (v : W64)
    (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (hj : j < 64) (bzz : zz < 2 ^ 64) (bzzl : zzl < 2 ^ 64) (bzzc : zzc < 2 ^ 64)
    (bq : q < 2 ^ 64) (bql : ql < 2 ^ 64) (bqc : qc < 2 ^ 64) (brl : rl < 2 ^ 64)
    (hb8 : M.readLE (sp + 0xb8) 8 = j) (h208 : M.readLE (sp + 0x208) 8 = xp) (h200 : M.readLE (sp + 0x200) 8 = st)
    (h218 : M.readLE (sp + 0x218) 8 = xc) (h1c0 : M.readLE (sp + 0x1c0) 8 = yl)
    (h1b8 : M.readLE (sp + 0x1b8) 8 = yp) (h138 : M.readLE (sp + 0x138) 8 = w)
    (h210 : M.readLE (sp + 0x210) 8 = xl)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 j1) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h8 : S.regs 8 = BitVec.ofNat 64 zz) (h6 : S.regs 6 = BitVec.ofNat 64 zzl) (h7 : S.regs 7 = BitVec.ofNat 64 zzc)
    (h15 : S.regs 15 = BitVec.ofNat 64 q) (h11 : S.regs 11 = BitVec.ofNat 64 ql) (h9 : S.regs 9 = BitVec.ofNat 64 qc)
    (h12 : S.regs 12 = BitVec.ofNat 64 rl) (h2 : S.regs 2 = v)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 t1 → T.regs 4 = BitVec.ofNat 64 sp →
      MemFrame M T.mem (wsJ1 sp) → T.mem.regions = M.regions →
      T.mem.readLE (sp + 0xa8) 8 = qc → T.mem.readLE (sp + 0xa0) 8 = ql → T.mem.readLE (sp + 0x90) 8 = rl →
      T.mem.readLE (sp + 0x168) 8 = q → T.mem.readLE (sp + 0x78) 8 = zzc → T.mem.readLE (sp + 0x70) 8 = zzl →
      T.mem.readLE (sp + 0x150) 8 = zz →
      T.regs 0 = S.regs 0 → T.regs 10 = S.regs 3 → T.regs 8 = S.regs 1 → T.regs 2 = S.regs 13 →
      T.regs 1 = BitVec.ofNat 64 (j + 1) → T.regs 13 = v + v → T.regs 15 = BitVec.ofNat 64 w →
      T.regs 3 = BitVec.ofNat 64 xl → T.regs 6 = BitVec.ofNat 64 xp → T.regs 7 = BitVec.ofNat 64 st →
      T.regs 9 = BitVec.ofNat 64 xc → T.regs 11 = BitVec.ofNat 64 yl → T.regs 12 = BitVec.ofNat 64 yp →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have ej : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x13 : S.regs 13 = r13 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem h2
  janus64_run [hb8, h208, h200, h218, h1c0, h1b8, h138, h210, ej] until [t1]
  refine K _ rfl ?g4 ?mf ?rg ?ma8 ?ma0 ?m90 ?m168 ?m78 ?m70 ?m150 ?r0 ?r10 ?r8 ?r2 ?r1 ?r13 ?r15 ?r3 ?r6 ?r7 ?r9 ?r11
    ?r12 ?g14 ?gfs ?gx ?gdf
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x70, sp + 0x80)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x90, sp + 0x98)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa0, sp + 0xb0)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x150, sp + 0x158)) (by simp) (by simp only; omega)
          (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x168, sp + 0x170)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case gfs => exact xf
  case gx => exact xx
  case g4 => janus64_simp
  case g14 => janus64_simp
  case gdf => janus64_simp
  case r0 => janus64_simp
  case r10 => janus64_simp
  case r8 => janus64_simp
  case r2 => janus64_simp
  case r1 => janus64_simp
  case r13 => janus64_simp
  case r15 => janus64_simp
  case r3 => janus64_simp
  case r6 => janus64_simp
  case r7 => janus64_simp
  case r9 => janus64_simp
  case r11 => janus64_simp
  case r12 => janus64_simp
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

end FvModexp.Amd64.ExpSlow
