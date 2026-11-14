import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure run of U1 — `t1` (`j < w`) → the `nat.sqr` entry (agent expmc s81)

`CMPQ CX, R15; JGE t1x` (not taken), spills `R8 → 0x130`, `DX → 0x98`, `R10 → 0x128`, `AX → 0x188`, `CX → 0xb8`,
`R13 → 0x88`, `BX = [0x70]`, `CX = [0x78]`, `SI = AX`, `R9 = R8`, `AX = [0x150]`, `R8 = R10`, `CALL nat.sqr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- U1's stores (return address and the six spills) -/
@[reducible] def wsU1 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x88, sp + 0x90), (sp + 0x98, sp + 0xa0), (sp + 0xb8, sp + 0xc0), (sp + 0x128, sp + 0x138),
    (sp + 0x188, sp + 0x190)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `t1` → `nat.sqr` entry -/
theorem runU1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp j w z zl zc' zz zzl zzc rc : Nat)
    (v : W64) (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (hjw : j < w) (hw : w ≤ 63) (hz : z < 2 ^ 64) (hzl : zl < 2 ^ 64)
    (hzc : zc' < 2 ^ 64) (hrc : rc < 2 ^ 64)
    (h150 : M.readLE (sp + 0x150) 8 = zz) (h70 : M.readLE (sp + 0x70) 8 = zzl) (h78 : M.readLE (sp + 0x78) 8 = zzc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 t1) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h1 : S.regs 1 = BitVec.ofNat 64 j) (h15 : S.regs 15 = BitVec.ofNat 64 w) (h0 : S.regs 0 = BitVec.ofNat 64 z)
    (h10 : S.regs 10 = BitVec.ofNat 64 zl) (h8 : S.regs 8 = BitVec.ofNat 64 zc') (h2 : S.regs 2 = BitVec.ofNat 64 rc)
    (h13 : S.regs 13 = v)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 6229984 → T.regs 4 = BitVec.ofNat 64 (sp - 8) →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      MemFrame M T.mem (wsU1 sp) → T.mem.regions = M.regions → T.mem.readLE (sp - 8) 8 = sq1R →
      T.mem.readLE (sp + 0x130) 8 = zc' → T.mem.readLE (sp + 0x98) 8 = rc → T.mem.readLE (sp + 0x128) 8 = zl →
      T.mem.readLE (sp + 0x188) 8 = z → T.mem.readLE (sp + 0xb8) 8 = j → T.mem.readLE (sp + 0x88) 8 = v.toNat →
      T.regs 0 = BitVec.ofNat 64 zz → T.regs 3 = BitVec.ofNat 64 zzl → T.regs 1 = BitVec.ofNat 64 zzc →
      T.regs 7 = S.regs 7 → T.regs 6 = BitVec.ofNat 64 z → T.regs 8 = BitVec.ofNat 64 zl →
      T.regs 9 = BitVec.ofNat 64 zc' → ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hj64 : j < 2 ^ 63 := by omega
  have hw64 : w < 2 ^ 63 := by omega
  generalize x7 : S.regs 7 = r7 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem h13
  janus64_run [e4, h150, h70, h78] until [6229984]
  refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x88, sp + 0x90)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x98, sp + 0xa0)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xb8, sp + 0xc0)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x128, sp + 0x138)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x188, sp + 0x190)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip
  all_goals simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | skip

end FvModexp.Amd64.ExpSlow
