import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFCE

/-! (Q-form copy of Arm64/Nat/DrsFC6R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final correction loop: the back edge (natdiv.go:869)

`c6rF`: from `0x1baaa4` (reached by the `e ≤ 0` jump after `nat.cmp` and by the `JMP` after `addTo(u[s:], v[s:])`):
`i++` (from the slot `SP'+232`), the reloads of `qhatv` → the head `CF` at `i + 1` (adapted from DrsC6R).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

/-- the back edge of the final correction loop -/
abbrev cBackF : Nat := 0x1baaa4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the back edge**: `i++` → `CF (i + 1)` at the model state `st` -/
theorem c6rF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 cBackF) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv3 : V3F c s T.mem qv (c.PF s U).length)
    (hsi : T.mem.readLE (s.sp.toNat - 168) 8 = i) (hi : i < 2)
    (hinv : Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length (2 - (i + 1)) st = c.sFF s U)
    (k : ∀ S', CF R c s Lk bk S' j Z U qv (i + 1) st → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r0 := hsi; have r1 := hv3.s320; have r2 := hv3.s144; have r3 := hv3.s160
  have hB1 : Box (McF R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  have hB2 : Box (V3F c s T.mem qv (c.PF s U).length) := ⟨hv3⟩
  have e3 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  clear hmc hv3
  janus_run [r0, r1, r2, r3] until [cHeadF]
  refine k _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hB1.1, hB2.1, by omega, hinv⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18
  · exact e3

end FvModexp.Arm64.Q.DivRec
