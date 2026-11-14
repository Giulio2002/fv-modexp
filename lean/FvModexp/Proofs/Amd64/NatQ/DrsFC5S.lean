import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC5S.lean; adapted from Amd64/NatQ/DrsC5S.lean)
# `divRecursiveStep` (amd64), final correction loop: the join `0x5f04d1` to the `addTo(u[s:], v[s:])` call
(natdiv.go:877)

`c5sF`: from `subVW`'s return (`0x5f04d1`, `BxF … stb (stC …)`) → the loads of `u[s:]`, `v[s:]` (`BdF` slots, no bounds
check) → `CALL addTo` (`0x5f0500`, return `0x5f0505`), in `c5rF`'s `kA` form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5sF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rFW2)
    (hbx : BxF R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb))
    (kA : ∀ X : State, BxF R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)) → X.regs 3 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)) →
      X.regs 1 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1)) → X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
      X.regs 6 = BitVec.ofNat 64 (c.vl - (c.vl / 2 - 1)) → X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) →
      MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFA →
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
  have r7 := hmc.bd.ul
  have r9 := hmc.bd.up; have r10 := hmc.bd.uc; have r11 := hmc.bd.vp; have r12 := hmc.bd.vl
  have r13 := hmc.bd.vc
  have hB1 : Box (BxF R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb)) := ⟨hbx⟩
  clear hbx hmc hpre hcr
  janus64_run [r7, r9, r10, r11, r12, r13] until [addToC]
  refine kA _ hB1.h rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8
    (by unfold isR; janus_frame) (by janus64_simp) ?ra
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case r5 => exact h5
  case r14 => exact h14
  case x15 => exact hx15
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
