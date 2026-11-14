import FvModexp.Proofs.Arm64.Nat.DrsSegD
/-!
# `divRecursiveStep` (arm64), final correction loop: to `CALL addTo(u[s:], v[s:])` (natdiv.go:876)
`c5sF`: from `0x1babb0` (both branches of the `len(qhatv) > s` test) → the six argument loads (`u[s:]`, `v[s:]` from the
final block's slots) → `CALL addTo` (`0x1babc8`, return `0x1babcc`). Adapted from DrsC5S.
-/
set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5sF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFA)
    (hbx : BxF R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb))
    (kA : ∀ X : State, X.pc = BitVec.ofNat 64 addToA → X.regs 30 = BitVec.ofNat 64 rFA2 →
      X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)) → X.regs 1 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)) →
      X.regs 2 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1)) → X.regs 3 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
      X.regs 4 = BitVec.ofNat 64 (c.vl - (c.vl / 2 - 1)) → X.regs 5 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) →
      BxF R c s Lk bk X j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hsp := hbx.sp; have h28 := hbx.r28; have h29 := hbx.r29; have h18 := hbx.r18
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hmc.bd.up; have r2 := hmc.bd.ul; have r3 := hmc.bd.uc; have r4 := hmc.bd.vp
  have r5 := hmc.bd.vl; have r6 := hmc.bd.vc
  have hB1 : Box (McF R c s Lk bk T.mem j Z U qv (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb)) := ⟨hbx.mc⟩
  have hB2 : Box (V3F c s T.mem qv (c.PF s U).length) := ⟨hbx.v3⟩
  have hsi := hbx.si; have hi := hbx.hi; have hpos := hbx.pos; have hinv := hbx.inv
  clear hbx hmc
  janus_run [r1, r2, r3, r4, r5, r6] until [addToA]
  refine kA _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ⟨rfl, ?_, ?_, ?_, hB1.1, hB2.1, hsi, hi, hpos, hinv⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18

end FvModexp.Arm64.DivRec
