import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsB4C
import FvModexp.Proofs.Arm64.NatQ.DrsB4R

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsB4.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), loop body segment 4: `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831)

`b4`: from `A3` (`0x1ba684`, after `clear(qhatv)`) → the argument loads → `CALL nat.mul` (`b4c`, DrsB4C) → the
stores of the result (`b4r`, DrsB4R) → the correction loop's head `C` (`0x1ba700`) at the model state `Cx.st0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **segment 4**: `A3` → `nat.mul` → `C` (`i = 0`, `Cx.st0`) -/
theorem b4 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypQE impl R ns stkM aboveM mulCQ) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hA : A3 R c s Lk bk S j Z U qn) (Q : State → Prop)
    (k : ∀ L' b' S', C R c s L' b' S' j Z U (c.qv s S.mem) 0 (c.st0 s j U) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have kT : ∀ T : State, T.pc = BitVec.ofNat 64 r4 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 → T.regs 0 = BitVec.ofNat 64 (c.qv s S.mem) →
      T.regs 1 = BitVec.ofNat 64 (c.P s j U).length → T.regs 2 = BitVec.ofNat 64 (3 * c.vl) →
      (∃ L' b', Mc R c s L' b' T.mem j Z U (c.qv s S.mem) (c.st0 s j U)) → c.qv s S.mem < 2 ^ 64 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q :=
    fun T h1 h2 h3 h4 h5 h6 h7 h8 ⟨L', b', hmc⟩ hqv =>
      b4r impl hap R c s L' b' j Z U _ Q T h1 h2 h3 h4 h5 h6 h7 h8 hmc hqv (k L' b')
  have hB : Box (A3 R c s Lk bk S j Z U qn) := ⟨hA⟩
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hpc := hA.pc; have hsp := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hA.v3.s328; have r2 := hA.v3.s152; have r3 := hA.v3.s168; have r4' := hsl.s4
  have r5 := hsl.q0p; have r6 := hA.q3.s208; have r7 := hsl.q0c; have r8 := hsl.s8; have r9 := hA.bs.b1
  have r10 := hsl.s10
  clear hA hcr hsl k
  janus_run [r1, r2, r3, r4', r5, r6, r7, r8, r9, r10] until [segAddr Extracted.program EvenHyp.fnMul]
  refine b4c impl hap R ns hns hcode hmul hk ha c s Lk bk S j Z U qn hB.1 Q _ rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ rfl kT
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18

end FvModexp.Arm64.Q.DivRec
