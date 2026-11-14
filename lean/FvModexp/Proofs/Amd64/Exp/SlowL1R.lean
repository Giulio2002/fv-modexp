import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the pure run of L1 — `t2` (`j < 64`) → the `nat.sqr` entry (agent asm s75; twin of
expmc's `SlowU1R`)

`MOVQ 0xb0(SP), R12; CMPQ R12, $0x40; JGE iS` (not taken), spills `R9 → 0x88` (v), `R13 → 0x100` (len q),
`R15 → 0xf8` (cap q), `CX → 0xf0` (len r), `DX → 0xe8` (cap r), `AX → 0x170` (z), `R10 → 0xe0` (len z),
`R8 → 0xd8` (cap z), `BX = [0x70]`, `CX = [0x78]`, `SI = AX`, `R9 = R8`, `AX = [0x150]`, `R8 = R10`, `CALL nat.sqr`
(return `sq2R` = `fnE + 0x5fb`); go-bigmodexpfix nat.go:769-770.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- L1's stores (return address and the eight spills) -/
@[reducible] def wsL1 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x88, sp + 0x90), (sp + 0xd8, sp + 0x108), (sp + 0x170, sp + 0x178)]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `t2` → `nat.sqr` entry -/
theorem runL1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp j z zl zc' zz zzl zzc rl rc ql qc : Nat)
    (v : W64) (M : Memory) (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp)
    (hsp2 : sp + 0x220 ≤ 2 ^ 48) (hjw : j < 64) (hz : z < 2 ^ 64) (hzl : zl < 2 ^ 64)
    (hzc : zc' < 2 ^ 64) (hrl : rl < 2 ^ 64) (hrc : rc < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64)
    (hb0 : M.readLE (sp + 0xb0) 8 = j)
    (h150 : M.readLE (sp + 0x150) 8 = zz) (h70 : M.readLE (sp + 0x70) 8 = zzl) (h78 : M.readLE (sp + 0x78) 8 = zzc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 t2) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z) (h10 : S.regs 10 = BitVec.ofNat 64 zl) (h8 : S.regs 8 = BitVec.ofNat 64 zc')
    (h1 : S.regs 1 = BitVec.ofNat 64 rl) (h2 : S.regs 2 = BitVec.ofNat 64 rc)
    (h13 : S.regs 13 = BitVec.ofNat 64 ql) (h15 : S.regs 15 = BitVec.ofNat 64 qc) (h9 : S.regs 9 = v)
    (K : ∀ T : State, T.rip = BitVec.ofNat 64 6229984 → T.regs 4 = BitVec.ofNat 64 (sp - 8) →
      T.regs 14 = S.regs 14 → T.fsBase = S.fsBase → T.xmm 15 = S.xmm 15 → T.df = S.df →
      MemFrame M T.mem (wsL1 sp) → T.mem.regions = M.regions → T.mem.readLE (sp - 8) 8 = sq2R →
      T.mem.readLE (sp + 0x88) 8 = v.toNat → T.mem.readLE (sp + 0x100) 8 = ql → T.mem.readLE (sp + 0xf8) 8 = qc →
      T.mem.readLE (sp + 0xf0) 8 = rl → T.mem.readLE (sp + 0xe8) 8 = rc → T.mem.readLE (sp + 0x170) 8 = z →
      T.mem.readLE (sp + 0xe0) 8 = zl → T.mem.readLE (sp + 0xd8) 8 = zc' →
      T.regs 0 = BitVec.ofNat 64 zz → T.regs 3 = BitVec.ofNat 64 zzl → T.regs 1 = BitVec.ofNat 64 zzc →
      T.regs 7 = S.regs 7 → T.regs 6 = BitVec.ofNat 64 z → T.regs 8 = BitVec.ofNat 64 zl →
      T.regs 9 = BitVec.ofNat 64 zc' → ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hj64 : j < 2 ^ 63 := by omega
  generalize x7 : S.regs 7 = r7 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem h9
  janus64_run [e4, hb0, h150, h70, h78, BitVec.msb_eq_decide] until [6229984]
  refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x88, sp + 0x90)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xd8, sp + 0x108)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x170, sp + 0x178)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals first | (janus64_simp; done) | rfl | exact xf | exact xx | skip
  all_goals simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | skip

end FvModexp.Amd64.ExpSlow
