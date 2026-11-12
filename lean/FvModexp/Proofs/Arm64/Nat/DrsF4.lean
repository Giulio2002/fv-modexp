import FvModexp.Proofs.Arm64.Nat.DrsF4C
import FvModexp.Proofs.Arm64.Nat.DrsF4R

/-!
# `divRecursiveStep` (arm64), final block segment 4: `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:867)

`f4`: from `AF3` (`0x1baa64`, after `clear(qhatv)`) → the argument loads → `CALL nat.mul` (`b4cF`) → the stores of the
result (`b4rF`) → the final correction loop's head `CF` (`0x1baab8`) at the model state `Cx.sF0`. Adapted from DrsB4.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **final segment 4**: `AF3` → `nat.mul` → `CF` (`i = 0`, `Cx.sF0`) -/
theorem f4 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypXE impl R ns stkM aboveM mulC) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hA : AF3 R c s Lk bk S j Z U qn) (Q : State → Prop)
    (k : ∀ L' b' S', CF R c s L' b' S' j Z U (c.qv s S.mem) 0 (c.sF0 s U) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have kT : ∀ T : State, T.pc = BitVec.ofNat 64 rF4 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 → T.regs 0 = BitVec.ofNat 64 (c.qv s S.mem) →
      T.regs 1 = BitVec.ofNat 64 (c.PF s U).length → T.regs 2 = BitVec.ofNat 64 (3 * c.vl) →
      (∃ L' b', McF R c s L' b' T.mem j Z U (c.qv s S.mem) (c.sF0 s U)) → c.qv s S.mem < 2 ^ 64 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q :=
    fun T h1 h2 h3 h4 h5 h6 h7 h8 ⟨L', b', hmc⟩ hqv =>
      b4rF impl hap R c s L' b' j Z U _ Q T h1 h2 h3 h4 h5 h6 h7 h8 hmc hqv (k L' b')
  have hB : Box (AF3 R c s Lk bk S j Z U qn) := ⟨hA⟩
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
  have r1 := hA.v3.s320; have r2 := hA.v3.s144; have r3 := hA.v3.s160; have r4' := hsl.s4
  have r5 := hsl.q0p; have r6 := hA.q3.s200; have r7 := hsl.q0c; have r8 := hsl.s8; have r9 := hA.bd.ss
  have r10 := hsl.s10
  clear hA hcr hsl k
  janus_run [r1, r2, r3, r4', r5, r6, r7, r8, r9, r10] until [segAddr Extracted.program EvenHyp.fnMul]
  refine b4cF impl hap R ns hns hcode hmul hk ha c s Lk bk S j Z U qn hB.1 Q _ rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ rfl kT
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18

end FvModexp.Arm64.DivRec
