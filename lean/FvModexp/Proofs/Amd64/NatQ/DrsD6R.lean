import FvModexp.Proofs.Amd64.NatQ.DrsSegD
import FvModexp.Proofs.Amd64.NatQ.DrsDV
import FvModexp.Proofs.Common.MaskWord

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsD6R.lean)
# `divRecursiveStep` (amd64), end of an iteration: the `addTo(z[j-B:], qhat)` call setup (natdiv.go:851)

`d6r`: from the join `0x5f003f` (`rJ6`, `Mc … stG`): `CMPQ BX, DX; JB` (`j - B ≤ len z`), `AX = qp + (mask & 8(j-B))`,
`BX = ql - (j-B)`, `CX = qc - (j-B)`, `DI = t0`, `SI = len qhat`, `R8 = B + 1` → `CALL addTo` (`0x5f00a8`, return
`0x5f00ad` = `rD6`). The only store is the return slot `r - 400`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d6r (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rJ6) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : Mc R c s Lk bk T.mem j Z U qv (c.stG s j U))
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 (c.qp + 8 * (j - c.vl / 2)) → X.regs 3 = BitVec.ofNat 64 (c.ql - (j - c.vl / 2)) →
      X.regs 1 = BitVec.ofNat 64 (c.qc - (j - c.vl / 2)) → X.regs 7 = BitVec.ofNat 64 c.t0 →
      X.regs 6 = BitVec.ofNat 64 (c.q0 s j U).length → X.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rD6 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hqlc := hpre.qlc; have hqc40 := hpre.qc40; have hq48 := hpre.qa.2.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hroom := (room hcr).1
  have hjB := hmc.jB
  have hgt : (BitVec.ofNat 64 c.ql < BitVec.ofNat 64 (j - c.vl / 2)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show c.ql < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j - c.vl / 2 < 2 ^ 64 by omega)]
    omega
  have r1 := hmc.bd.sl.s1; have r2 := hmc.bd.sl.s2; have r3 := hmc.bd.sl.s3; have r4 := hmc.bd.sj
  have r5 := hmc.bd.sj8; have r6 := hmc.bd.sl.q0p; have r7 := hmc.q3.s208; have r8 := hmc.bd.sl.q0c
  have e1 := bvS2 (a := j - c.vl / 2) (u := c.ql) (by omega) (by omega)
  have e2 := bvS2 (a := j - c.vl / 2) (u := c.qc) (by omega) (by omega)
  have e3 := bvM (q := c.qp) (k := 8 * (j - c.vl / 2)) (x := c.qc - (j - c.vl / 2)) (by omega) (by omega)
    (by omega) (by omega)
  have hB : Box (Mc R c s Lk bk T.mem j Z U qv (c.stG s j U)) := ⟨hmc⟩
  clear hmc hpre hcr
  janus64_run [r1, r2, r3, r4, r5, r6, r7, r8, hgt, e1, e2, e3] until [addToC]
  refine k _ rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8
    (by unfold isR; janus_frame) (by janus64_simp) ?ra
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case r5 => exact h5
  case r14 => exact h14
  case x15 => exact hx15
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
