import FvModexp.Proofs.Amd64.Exp.SlowDefs
import FvModexp.Proofs.Common.ExpBase
import FvModexp.Proofs.Common.Util

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the run `aSet` → `t1` (agent expmc s80; twin of arm64 `SlowPV`'s run)

At `aSet` (`fnE + 0x148`, nat.go:734-749): `LEAQ -1(R11), R12; CMPQ R11, R12; JBE panic` (`len y ≥ 1`),
`R13 = y[len y - 1]`, `BSRQ R13, R15` (`CMOVE`: `-1` when `0`), spill `[0x138] = R15`, `shift = 63 - R15 + 1`,
`R13 <<= shift` (`SBBQ` mask: `0` when `shift = 64`), `j = CX = 0`, `rc = DX = 0`, the eight zero slots
`0xa8 0xa0 0x90 0x168 0x160 0x78 0x70 0x150`, `JMP t1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- `runV`'s writes -/
@[reducible] def FV (sp : Nat) : List (Nat × Nat) :=
  [(sp + 0x138, sp + 0x140), (sp + 0xa8, sp + 0xb0), (sp + 0xa0, sp + 0xa8), (sp + 0x90, sp + 0x98),
    (sp + 0x168, sp + 0x170), (sp + 0x160, sp + 0x168), (sp + 0x78, sp + 0x80), (sp + 0x70, sp + 0x78),
    (sp + 0x150, sp + 0x158)]

/-- the initial `w` (bits of the top word below its leading one) -/
@[reducible] def wN (t : Nat) : Nat := 64 - ((64 - Exp.bitLen t) + 1)

/-- the initial `v` (the top word shifted past its leading one) -/
@[reducible] def vN (t : Nat) : Nat := t * 2 ^ ((64 - Exp.bitLen t) + 1) % Exp.B

theorem clz_bl' (t : Nat) (ht : t < 2 ^ 64) (ht0 : t ≠ 0) :
    Arm64.clzNat 64 t + Exp.bitLen t = 64 ∧ 1 ≤ Exp.bitLen t := by
  have hc := Util.clz_bl 64 t ht
  have eb : Exp.bitLen t = Aux.bitLen t := by unfold Exp.bitLen Aux.bitLen; rfl
  have hb : 1 ≤ Aux.bitLen t := by unfold Aux.bitLen; rw [if_neg ht0]; omega
  rw [eb]; exact ⟨hc, hb⟩

theorem v_val (t c : Nat) (ht : t < 2 ^ 64) (hc : c + Exp.bitLen t = 64) (hb : 1 ≤ Exp.bitLen t) :
    (BitVec.ofNat 64 t <<< ((c + 1) % 64) &&& (if c + 1 < 64 then 18446744073709551615#64 else 0#64)).toNat =
      vN t := by
  unfold vN
  rw [Exp.B_def, show 64 - Exp.bitLen t + 1 = c + 1 by omega]
  split
  · rw [Nat.mod_eq_of_lt (by omega : c + 1 < 64)]
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt ht, show (18446744073709551615 : Nat) % 2 ^ 64 = 2 ^ 64 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  · have e : c + 1 = 64 := by omega
    rw [e, Nat.mul_mod_left]; simp

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `aSet` → `t1` -/
theorem runV {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp yp yl t : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (hyl0 : 0 < yl) (hyl : yl ≤ 2 ^ 9) (h1c0 : M.readLE (sp + 0x1c0) 8 = yl) (h1b8 : M.readLE (sp + 0x1b8) 8 = yp)
    (hya : M.accessible (yp + yl * 8 - 8) 8 false = true) (hyt : M.readLE (yp + yl * 8 - 8) 8 = t)
    (ht0 : t ≠ 0) (ht : t < 2 ^ 64) (hy48 : yp + 8 * yl ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 aSet) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 t1 → S'.regs 4 = BitVec.ofNat 64 sp →
      MemFrame M S'.mem (FV sp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp + 0x138) 8 = wN t →
      S'.mem.readLE (sp + 0xa8) 8 = 0 → S'.mem.readLE (sp + 0xa0) 8 = 0 → S'.mem.readLE (sp + 0x90) 8 = 0 →
      S'.mem.readLE (sp + 0x168) 8 = 0 → S'.mem.readLE (sp + 0x160) 8 = 0 → S'.mem.readLE (sp + 0x78) 8 = 0 →
      S'.mem.readLE (sp + 0x70) 8 = 0 → S'.mem.readLE (sp + 0x150) 8 = 0 →
      S'.regs 0 = S.regs 0 → S'.regs 1 = BitVec.ofNat 64 0 → S'.regs 2 = BitVec.ofNat 64 0 →
      S'.regs 3 = S.regs 2 → S'.regs 8 = S.regs 1 → S'.regs 10 = S.regs 10 → S'.regs 6 = S.regs 6 →
      S'.regs 7 = S.regs 7 → S'.regs 9 = S.regs 9 → S'.regs 11 = BitVec.ofNat 64 yl →
      S'.regs 12 = BitVec.ofNat 64 yp → (S'.regs 13).toNat = vN t → S'.regs 15 = BitVec.ofNat 64 (wN t) →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hsub : BitVec.ofNat 64 yl - 1#64 = BitVec.ofNat 64 (yl - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hcb, hb1⟩ := clz_bl' t ht ht0
  have hw : BitVec.ofNat 64 (63 - Arm64.clzNat 64 t) = BitVec.ofNat 64 (wN t) := by
    unfold wN; congr 1; omega
  have hsh : (18446744073709551616 - (18446744073709551553 + (BitVec.ofNat 64 (63 - Arm64.clzNat 64 t)).toNat) %
      18446744073709551616) % 18446744073709551616 + 1 = Arm64.clzNat 64 t + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  have hT : (BitVec.ofNat 64 (63 - Arm64.clzNat 64 t)).toNat = 63 - Arm64.clzNat 64 t := by
    rw [BitVec.toNat_ofNat]; omega
  have e1 : (18446744073709551616 - (18446744073709551553 + (63 - Arm64.clzNat 64 t)) % 18446744073709551616) %
      18446744073709551616 = Arm64.clzNat 64 t := by omega
  have e2 : (18446744073709551616 - (18446744073709551553 + (63 - Arm64.clzNat 64 t)) % 18446744073709551616 + 1) %
      18446744073709551616 = Arm64.clzNat 64 t + 1 := by omega
  have hwb : wN t < 64 := by unfold wN; omega
  have hcl : Arm64.clzNat 64 t < 18446744073709551616 := by omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x2 : S.regs 2 = r2 at K
  generalize x6 : S.regs 6 = r6 at K
  generalize x7 : S.regs 7 = r7 at K
  generalize x9 : S.regs 9 = r9 at K
  generalize x10 : S.regs 10 = r10 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hacc, hya, h1c0, h1b8, hyt, hsub] until [t1]
  refine K _ ?rip ?r4 ?mf ?rg ?m138 ?ma8 ?ma0 ?m90 ?m168 ?m160 ?m78 ?m70 ?m150 ?g0 ?g1 ?g2 ?g3 ?g8 ?g10 ?g6 ?g7 ?g9 ?g11 ?g12 ?v ?g15 ?g14 ?gfs ?gx ?gdf
  case rip => rfl
  case r4 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact h4 | rfl
  case mf =>
    repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x138, sp + 0x140)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa8, sp + 0xb0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa0, sp + 0xa8)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x90, sp + 0x98)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x168, sp + 0x170)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x160, sp + 0x168)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x78, sp + 0x80)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x70, sp + 0x78)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x150, sp + 0x158)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case m138 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] <;>
    simp only [ht0, if_false, ↓reduceIte, hw, BitVec.toNat_ofNat, Nat.reducePow] <;> omega
  case ma8 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case ma0 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m90 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m168 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m160 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m78 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m70 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m150 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case g0 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x0 | rfl
  case g1 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g2 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g3 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x2 | rfl
  case g8 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x1 | rfl
  case g10 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x10 | rfl
  case g6 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x6 | rfl
  case g7 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x7 | rfl
  case g9 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x9 | rfl
  case g11 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g12 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g15 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; simp only [ht0, if_false, ↓reduceIte, hw]
  case g14 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x14 | rfl
  case gfs => exact xf
  case gx => exact xx
  case gdf => rfl
  case v =>
    show (_ : W64).toNat = vN t
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, ht0, if_false, hT]
    first
      | (rw [e1]; exact v_val t _ ht hcb hb1)
      | (simp only [ht0, if_false, ↓reduceIte, hT] at hbr
         rw [e1] at hbr
         have h63 : Arm64.clzNat 64 t = 63 := by omega
         rw [e2, show Arm64.clzNat 64 t + 1 = 64 by omega]
         unfold vN
         rw [Exp.B_def, show 64 - Exp.bitLen t + 1 = 64 by omega, Nat.mul_mod_left]
         simp)
  refine K _ ?rip ?r4 ?mf ?rg ?m138 ?ma8 ?ma0 ?m90 ?m168 ?m160 ?m78 ?m70 ?m150 ?g0 ?g1 ?g2 ?g3 ?g8 ?g10 ?g6 ?g7 ?g9 ?g11 ?g12 ?v ?g15 ?g14 ?gfs ?gx ?gdf
  case rip => rfl
  case r4 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact h4 | rfl
  case mf =>
    repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x138, sp + 0x140)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa8, sp + 0xb0)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xa0, sp + 0xa8)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x90, sp + 0x98)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x168, sp + 0x170)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x160, sp + 0x168)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x78, sp + 0x80)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x70, sp + 0x78)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x150, sp + 0x158)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case m138 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] <;>
    simp only [ht0, if_false, ↓reduceIte, hw, BitVec.toNat_ofNat, Nat.reducePow] <;> omega
  case ma8 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case ma0 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m90 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m168 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m160 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m78 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m70 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case m150 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case g0 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x0 | rfl
  case g1 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g2 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g3 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x2 | rfl
  case g8 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x1 | rfl
  case g10 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x10 | rfl
  case g6 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x6 | rfl
  case g7 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x7 | rfl
  case g9 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x9 | rfl
  case g11 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g12 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | rfl | rfl
  case g15 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; simp only [ht0, if_false, ↓reduceIte, hw]
  case g14 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> first | exact x14 | rfl
  case gfs => exact xf
  case gx => exact xx
  case gdf => rfl
  case v =>
    show (_ : W64).toNat = vN t
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, ht0, if_false, hT]
    first
      | (rw [e1]; exact v_val t _ ht hcb hb1)
      | (simp only [ht0, if_false, ↓reduceIte, hT] at hbr
         rw [e1] at hbr
         have h63 : Arm64.clzNat 64 t = 63 := by omega
         rw [e2, show Arm64.clzNat 64 t + 1 = 64 by omega]
         unfold vN
         rw [Exp.B_def, show 64 - Exp.bitLen t + 1 = 64 by omega, Nat.mul_mod_left]
         simp)

end FvModexp.Amd64.ExpSlow
