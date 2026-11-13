import FvModexp.Proofs.Amd64.NatQ.DrsC3

set_option autoImplicit false

/-! (amd64 twin (asm s49) of Arm64/NatQ/DrsC4R.lean)
# `divRecursiveStep` (amd64), correction loop: to `CALL subVV.abi0(qhatv[:s], qhatv[:s], v[:s])` (natdiv.go:838)

`c4r`: from `subVW`'s return (`0x5efe35`, `Bx … stb st`) → `CMPQ DX, R10; JB` (`s ≤ cap qhatv = 3n`; `DX = 0x98(SP')`,
`R10 = 0x78(SP')` = `s`) → the nine argument words at `0(SP') … 64(SP')` (`[r-392, r-320)`: `qhatv[:s]` twice, then
`v[:s]` = `(0x190(SP'), s, 0x1a0(SP'))` = `(vp, s, vc)`) → `CALL subVV.abi0` (`0x5efe8f`, return `0x5efe94`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- `subVV.abi0`'s entry -/
abbrev subVVA : Nat := segAddr Extracted.program Callees.subVVfn

/-- `subVV.abi0`'s return address -/
abbrev rV1 : Nat := 0x5efe94

/-- the return slot and the argument words of the `subVV.abi0` call (`[r-400, r-320)`) -/
@[reducible] def isA (s : State) : List (Nat × Nat) := [((s.regs 4).toNat - 400, (s.regs 4).toNat - 320)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c4r (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rW1) (hbx : Bx R c s Lk bk T j Z U qv i stb st)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 subVVA → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      MemFrame T.mem X.mem (isA s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rV1 →
      X.mem.readLE ((s.regs 4).toNat - 392) 8 = qv → X.mem.readLE ((s.regs 4).toNat - 384) 8 = c.vl / 2 - 1 →
      X.mem.readLE ((s.regs 4).toNat - 368) 8 = qv → X.mem.readLE ((s.regs 4).toNat - 344) 8 = c.vp →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1; have hvc40 := hpre.vc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsp := hbx.sp; have h5 := hbx.r5; have h14 := hbx.r14; have hfs := hbx.fs; have hdf := hbx.df
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hbx.v4.s168; have r2 := hmc.bs.b1; have r3 := hbx.v4.s328
  have r4 := hmc.bd.sl.vp; have r5 := hmc.bd.sl.vc
  have hqv : qv < 2 ^ 48 := by have := Janus.Arm64.Memory.accessible_bound _ hmc.qa; omega
  have hvp : c.vp < 2 ^ 48 := by have := hpre.va.2.1; omega
  have hlt : (BitVec.ofNat 64 (3 * c.vl) < BitVec.ofNat 64 (c.vl / 2 - 1)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show 3 * c.vl < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c.vl / 2 - 1 < 2 ^ 64 by omega)]
    omega
  clear hbx hmc
  janus64_run [r1, r2, r3, r4, r5, hlt] until [subVVA]
  refine k _ rfl ?sp ?r5 ?r14 hfs rfl (by unfold isA; janus_frame) (by janus64_simp) ?ra ?e1 ?e2 ?e3 ?e4
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  all_goals dsimp only
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e1 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e2 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e3 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e4 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
