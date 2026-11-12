import FvModexp.Proofs.Arm64.Exp.P2DDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the runs of `return z.setWord(x[0] & 1)` (`logM = 1`, nat.go:923) (agent infra)

From `oneE` (`0x1b59f0`): `len x = 0` panic (excluded), bit 0 of `x[0]`:
* `oneR0`: 0 → `R1 = 0`, epilogue (`z[:0]`);
* `oneR1`: 1, `cap z ≠ 0` → `z[0] = 1`, `R1 = 1`, epilogue;
* `oneRM`: 1, `cap z = 0` → the entry of `makeslice(Word, 1, 1)` (return `1792544`); `mkR` from there: `R2 = 1`,
  `[R0] = 1`, `R1 = 1`, epilogue.
Epilogue: `X29 = [sp - 8]`, `X30 = [sp]`, `SP = sp + 112`, `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

abbrev oneE' : Nat := 1792496
abbrev mkE : Nat := 587344
theorem mkE_eq : Extracted.program.contractAddr "runtime.makeslice" = mkE := by decide
abbrev mkRa : Nat := 1792544

/-- the epilogue facts at the memory `M` (frame `sp`) -/
@[reducible] def Epi (M : Memory) (sp r29 ret : Nat) : Prop :=
  sp % 16 = 0 ∧ 8 ≤ sp ∧ sp + 112 ≤ 2 ^ 48 ∧ M.accessible (sp - 8) 16 false = true ∧
    M.readLE (sp - 8) 8 = r29 ∧ M.readLE sp 8 = ret ∧ ret % 4 = 0 ∧ ret < 2 ^ 48

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem oneR0 (impl : List Segment) (Q : State → Prop) (sp xp xl r29 ret : Nat) (M : Memory)
    (he : Epi M sp r29 ret) (hxl : 0 < xl) (hxl' : xl < 2 ^ 64) (hxa : M.accessible xp 8 false = true)
    (hxp : xp < 2 ^ 64) (hx0 : M.readLE xp 8 % 2 = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneE') (hsp : S.sp = BitVec.ofNat 64 sp)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl) (hmem : S.mem = M)
    (KF : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 112) → s'.regs 0 = S.regs 0 → s'.regs 1 = 0#64 →
      s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 → s'.regs 28 = S.regs 28 →
      s'.regs 29 = BitVec.ofNat 64 r29 → s'.mem = M → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, rfp, rlr, hr4, hr48⟩ := he
  have hb : ((BitVec.ofNat 64 (M.readLE xp 8)).getLsbD 0 == true) = false := by
    rw [beq_eq_false_iff_ne, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_zero]; simp; omega
  generalize e0 : S.regs 0 = x0 at KF
  generalize e2 : S.regs 2 = x2 at KF
  generalize e18 : S.regs 18 = x18 at KF
  generalize e28 : S.regs 28 = x28 at KF
  subst hmem
  janus_run [hb, rfp, rlr]
  refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals janus_simp

theorem bit1 {v : Nat} (h : v % 2 = 1) : ((BitVec.ofNat 64 v).getLsbD 0 == true) = true := by
  rw [beq_iff_eq, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_zero, decide_eq_true_iff]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem oneR1 (impl : List Segment) (Q : State → Prop) (sp zp zc xp xl r29 ret : Nat) (M : Memory)
    (he : Epi M sp r29 ret) (hxl : 0 < xl) (hxl' : xl < 2 ^ 64) (hxa : M.accessible xp 8 false = true)
    (hxp : xp < 2 ^ 64) (hx0 : M.readLE xp 8 % 2 = 1) (hzc : 0 < zc) (hzc' : zc < 2 ^ 64) (hzp : zp < 2 ^ 64)
    (hza : M.accessible zp 8 true = true) (hzw : zp + 8 ≤ sp - 8 ∨ sp + 8 ≤ zp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneE') (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl) (hmem : S.mem = M)
    (KF : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 112) → s'.regs 0 = BitVec.ofNat 64 zp → s'.regs 1 = 1#64 →
      s'.regs 2 = BitVec.ofNat 64 zc → s'.regs 18 = S.regs 18 → s'.regs 28 = S.regs 28 →
      s'.regs 29 = BitVec.ofNat 64 r29 → s'.mem = M.writeLE zp 8 1 → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, rfp, rlr, hr4, hr48⟩ := he
  have hb := bit1 hx0
  have rfp' : (M.writeLE zp 8 1).readLE (sp - 8) 8 = r29 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rfp
  have rlr' : (M.writeLE zp 8 1).readLE sp 8 = ret := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rlr
  generalize e18 : S.regs 18 = x18 at KF
  generalize e28 : S.regs 28 = x28 at KF
  subst hmem
  janus_run [hb, rfp', rlr']
  refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem oneRM (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (sp xp xl : Nat) (M : Memory)
    (hxl : 0 < xl) (hxl' : xl < 2 ^ 64) (hxa : M.accessible xp 8 false = true)
    (hxp : xp < 2 ^ 64) (hx0 : M.readLE xp 8 % 2 = 1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneE') (hsp : S.sp = BitVec.ofNat 64 sp)
    (h2 : S.regs 2 = 0#64) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (hmem : S.mem = M)
    (KM : ∀ T : State, T.pc = BitVec.ofNat 64 mkE → T.sp = S.sp → T.regs 0 = 2641088#64 → T.regs 1 = 1#64 →
      T.regs 2 = 1#64 → T.regs 30 = BitVec.ofNat 64 mkRa → T.regs 18 = S.regs 18 → T.regs 28 = S.regs 28 →
      T.regs 29 = S.regs 29 → T.mem = M → ReachesRet (LibW.program.link impl) ret0 T Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hb := bit1 hx0
  generalize e18 : S.regs 18 = x18 at KM
  generalize e28 : S.regs 28 = x28 at KM
  generalize e29 : S.regs 29 = x29 at KM
  generalize eS : S.sp = xsp at KM
  subst hmem
  janus_run [hb] until [mkE]
  refine KM _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus_simp
  all_goals rw [← eS, hsp]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem mkR (impl : List Segment) (Q : State → Prop) (sp p r29 ret : Nat) (M : Memory)
    (he : Epi M sp r29 ret) (hp : p < 2 ^ 64) (hpa : M.accessible p 8 true = true)
    (hpw : p + 8 ≤ sp - 8 ∨ sp + 8 ≤ p)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mkRa) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (hmem : S.mem = M)
    (KF : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 112) → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = 1#64 →
      s'.regs 2 = 1#64 → s'.regs 18 = S.regs 18 → s'.regs 28 = S.regs 28 →
      s'.regs 29 = BitVec.ofNat 64 r29 → s'.mem = M.writeLE p 8 1 → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, rfp, rlr, hr4, hr48⟩ := he
  have rfp' : (M.writeLE p 8 1).readLE (sp - 8) 8 = r29 := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rfp
  have rlr' : (M.writeLE p 8 1).readLE sp 8 = ret := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rlr
  generalize e18 : S.regs 18 = x18 at KF
  generalize e28 : S.regs 28 = x28 at KF
  subst hmem
  janus_run [rfp', rlr']
  refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals janus_simp

end FvModexp.Arm64.P2D
