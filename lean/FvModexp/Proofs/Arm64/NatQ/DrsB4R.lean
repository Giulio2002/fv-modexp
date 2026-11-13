import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsB4D

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsB4R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), loop body segment 4 (after the call): `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831)

`b4r`: from the return state `T` of `nat.mul` (`0x1ba6b0`, `Mc` at the model state `Cx.st0`) → the stores of the
result `qhatv` (`SP'+328/152/168`), `i := 0` → the correction loop's head `C` (`0x1ba700`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- after `nat.mul` returns: the stores of `qhatv`'s slots and `i := 0` → `C` -/
theorem b4r (impl : List Segment) (_hap : ImplApart Extracted.program impl) (R : RtInv)
    (c : Cx) (s : State) (L' : List (Nat × Nat)) (b' : Nat) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hTpc : T.pc = BitVec.ofNat 64 r4) (hTsp : T.sp = s.sp - 400#64) (hT28 : T.regs 28 = s.regs 28)
    (hT29 : T.regs 29 = s.sp - 408#64) (hT18 : T.regs 18 = s.regs 18) (hr0 : T.regs 0 = BitVec.ofNat 64 qv)
    (hr1 : T.regs 1 = BitVec.ofNat 64 (c.P s j U).length) (hr2 : T.regs 2 = BitVec.ofNat 64 (3 * c.vl))
    (hmc : Mc R c s L' b' T.mem j Z U qv (c.st0 s j U)) (hqv : qv < 2 ^ 64)
    (k : ∀ S', C R c s L' b' S' j Z U qv 0 (c.st0 s j U) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn' : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl : (c.P s j U).length < 2 ^ 64 := by
    have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
      ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
    rw [Mdl.length_toL, List.length_take] at h1
    have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
    have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
    show (Mdl.norm _).length < _
    rw [List.length_take]
    omega
  have h3v : 3 * c.vl < 2 ^ 64 := by omega
  obtain ⟨e1, e2, e3⟩ := rd3 T.mem s.sp.toNat qv (c.P s j U).length (3 * c.vl) (by omega) hqv hPl h3v
  have hB : Box (Mc R c s L' b' T.mem j Z U qv (c.st0 s j U)) := ⟨hmc⟩
  clear hmc
  janus_run until [cHead]
  refine k _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hB.1.own3 (by unfold is3; janus_frame) (by simp),
    ⟨?_, ?_, ?_⟩, by omega, rfl⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact hT28
  · exact hT29
  · exact hT18
  · exact hr0
  · exact hr1
  · exact hr2
  all_goals (try dsimp only)
  · exact e1
  · exact e2
  · exact e3

end FvModexp.Arm64.Q.DivRec
