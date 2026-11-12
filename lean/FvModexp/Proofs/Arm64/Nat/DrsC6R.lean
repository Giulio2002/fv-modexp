import FvModexp.Proofs.Arm64.Nat.DrsCE

/-!
# `divRecursiveStep` (arm64), correction loop: `i++` back to the head (natdiv.go:832)

`c6r`: from `addTo`'s return (`0x1ba6ec`, `Bx … stb (corrOnce stb)`) → `R3 = i + 1`, reload `qhatv` → the head `C`
(`0x1ba700`) after `i + 1` corrections (`Bx.next`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c6r (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 0x1ba6ec)
    (hbx : Bx R c s Lk bk T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb))
    (k : ∀ S', C R c s Lk bk S' j Z U qv (i + 1) (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
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
  have r0 := hbx.si; have r1 := hbx.v4.s328; have r2 := hbx.v4.s152; have r3 := hbx.v4.s168
  have hi := hbx.hi
  have hinv := Bx.next hi hbx.pos hbx.inv
  have hB1 : Box (Mc R c s Lk bk T.mem j Z U qv (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb)) :=
    ⟨hbx.mc⟩
  have hB2 : Box (V4 c s T.mem qv (c.P s j U).length) := ⟨hbx.v4⟩
  have e3 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  clear hbx hmc
  janus_run [r0, r1, r2, r3] until [cHead]
  refine k _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hB1.1, hB2.1, by omega, hinv⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18
  · exact e3

end FvModexp.Arm64.DivRec
