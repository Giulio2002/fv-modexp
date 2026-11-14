import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsC5S.lean)
# `divRecursiveStep` (amd64), correction loop: after `subVW(qhatv[s:], …)` to the `addTo(uu[s:], v[s:])` call (natdiv.go:842)

`c5s`: from `subVW`'s return (`0x5eff0b`, `Bx … stb (stC …)`) → `AX = 0x78(SP')` (`s`), `SI = 0x88(SP')` → the join
`0x5eff18` (`CMPQ BX, AX; JAE`: `len uu ≥ s`) → `CALL addTo` (`0x5efd80`, return `0x5efd85`), in `c5r`'s `kA` form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5s (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rW2)
    (hbx : Bx R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb))
    (kA : ∀ X : State, Bx R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1)) → X.regs 3 = BitVec.ofNat 64 (c.u1 - j + 1) →
      X.regs 1 = BitVec.ofNat 64 (c.uc - (j - 1)) → X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
      X.regs 6 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1) → X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) →
      MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rA →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1; have hvc40 := hpre.vc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hul := hpre.ulc; have huc := hpre.uc40
  have hsp := hbx.sp; have h5 := hbx.r5; have h14 := hbx.r14; have hfs := hbx.fs; have hx15 := hbx.x15
  have hdf := hbx.df
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have r1 := hbx.v4.s152; have r2 := hmc.bs.b1
  have r5 := hmc.bd.sl.bb; have r7 := hmc.bd.sul
  have r9 := hmc.bs.uptr; have r10 := hmc.bs.ucap; have r11 := hmc.bs.vptr; have r12 := hmc.bs.vlen
  have r13 := hmc.bs.vcap
  have e1 : BitVec.ofNat 64 (c.u1 - (j - c.vl / 2)) - BitVec.ofNat 64 (c.vl / 2) + 1#64 =
      BitVec.ofNat 64 (c.u1 - j + 1) := by exact (bvA (by omega) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have t7 := tN (by omega : c.u1 - (j - c.vl / 2) < 2 ^ 64)
  have t8 := tN (by omega : c.vl / 2 - 1 < 2 ^ 64)
  have hB1 : Box (Bx R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb)) := ⟨hbx⟩
  clear hbx hmc hpre hcr
  janus64_run [r1, r2, r5, r7, r9, r10, r11, r12, r13, t7, t8, e1] until [addToC]
  refine kA _ hB1.h rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8
    (by unfold isR; janus_frame) (by janus64_simp) ?ra
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case r5 => exact h5
  case r14 => exact h14
  case x15 => exact hx15
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
