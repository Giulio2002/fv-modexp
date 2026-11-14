import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure run of the lower back-edge `j2` → `t2` (agent asm s75; nat.go:769, 783)

`ADDQ DX, DX` (`v <<= 1`), `[0xb0] += 1` (`j++`), `R10 = BX`, `[0x168] = R15`, `[0x70] = SI`, `[0x78] = DI`,
`[0x150] = R8` (`zz`, `q` spilled), `SI = [0x208]`, `DI = [0x200]`, `R8 = CX`, `R15 = R11`, `CX = R12`,
`R11 = [0xc0]`, `R9 = DX`, `DX = R13`, `R13 = R9`, `BX = [0x210]` → `t2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the back-edge's stores -/
@[reducible] def wsJ2 (sp : Nat) : List (Nat × Nat) :=
  [(sp + 0x70, sp + 0x80), (sp + 0xb0, sp + 0xb8), (sp + 0x150, sp + 0x158), (sp + 0x168, sp + 0x170)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `j2` → `t2` -/
theorem runJ2 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp j i xp xl st : Nat)
    (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (hj : j < 64)
    (hb0 : M.readLE (sp + 0xb0) 8 = j) (hc0 : M.readLE (sp + 0xc0) 8 = i) (h208 : M.readLE (sp + 0x208) 8 = xp)
    (h210 : M.readLE (sp + 0x210) 8 = xl) (h200 : M.readLE (sp + 0x200) 8 = st)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 j2) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 t2 → T.regs 4 = BitVec.ofNat 64 sp →
      MemFrame M T.mem (wsJ2 sp) → T.mem.regions = M.regions →
      T.mem.readLE (sp + 0xb0) 8 = j + 1 → T.mem.readLE (sp + 0x168) 8 = (S.regs 15).toNat →
      T.mem.readLE (sp + 0x70) 8 = (S.regs 6).toNat → T.mem.readLE (sp + 0x78) 8 = (S.regs 7).toNat →
      T.mem.readLE (sp + 0x150) 8 = (S.regs 8).toNat →
      T.regs 0 = S.regs 0 → T.regs 10 = S.regs 3 → T.regs 8 = S.regs 1 → T.regs 1 = S.regs 12 →
      T.regs 2 = S.regs 13 → T.regs 13 = S.regs 9 → T.regs 15 = S.regs 11 → T.regs 9 = S.regs 2 + S.regs 2 →
      T.regs 11 = BitVec.ofNat 64 i → T.regs 3 = BitVec.ofNat 64 xl → T.regs 6 = BitVec.ofNat 64 xp →
      T.regs 7 = BitVec.ofNat 64 st →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have ej : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x2 : S.regs 2 = r2 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x6 : S.regs 6 = r6 at K
  generalize x7 : S.regs 7 = r7 at K
  generalize x8 : S.regs 8 = r8 at K
  generalize x9 : S.regs 9 = r9 at K
  generalize x11 : S.regs 11 = r11 at K
  generalize x12 : S.regs 12 = r12 at K
  generalize x13 : S.regs 13 = r13 at K
  generalize x15 : S.regs 15 = r15 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hb0, hc0, h208, h210, h200, ej] until [t2]
  refine K _ rfl ?_ ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x70, sp + 0x80)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xb0, sp + 0xb8)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x150, sp + 0x158)) (by simp) (by simp only; omega)
          (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x168, sp + 0x170)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals first | (janus64_simp; done) | exact xf | exact xx | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

end FvModexp.Amd64.ExpSlow
