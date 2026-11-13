import FvModexp.Proofs.Amd64.NatQ.DrsB4C
import FvModexp.Proofs.Amd64.NatQ.DrsB4R

set_option autoImplicit false

/-! (amd64 twin (asm s48) of Arm64/NatQ/DrsB4.lean)
# `divRecursiveStep` (amd64), loop body segment 4: `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831)

`b4`: `A3` (`0x5efcc5`) → the argument loads, the stack arguments `v[:s]` (`0/8/0x10(SP)`), `CALL nat.mul`
(`0x5efd20`; `b4c`) → the stores of the result (`b4r`) → the correction loop's head `C` (`i = 0`, `Cx.st0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **segment 4**: `A3` → `nat.mul` → `C` (`i = 0`, `Cx.st0`) -/
theorem b4 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hA : A3 R c s Lk bk S j Z U qn)
    (Q : State → Prop)
    (k : ∀ L' b' S', C R c s L' b' S' j Z U (c.qv s S.mem) 0 (c.st0 s j U) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hq48 : c.qv s S.mem < 2 ^ 48 := by
    have hl := hA.fp.len; have hlc := hA.ev.sok.2.2.2.2.2.1
    have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
    have hn : 0 < stCap S.mem c.st := by omega
    obtain ⟨-, -, -, h48⟩ := hA.ev.sok.2.2.2.2.1 hn
    simp only [Cx.qv]; omega
  have kT : ∀ T : State, T.rip = BitVec.ofNat 64 r4 → T.regs 4 = s.regs 4 - 392#64 → T.regs 5 = s.regs 4 - 8#64 →
      T.regs 14 = s.regs 14 → T.fsBase = s.fsBase → T.df = false → T.xmm 15 = 0#128 →
      T.regs 0 = BitVec.ofNat 64 (c.qv s S.mem) → T.regs 3 = BitVec.ofNat 64 (c.P s j U).length →
      T.regs 1 = BitVec.ofNat 64 (3 * c.vl) →
      (∃ L' b', Mc R c s L' b' T.mem j Z U (c.qv s S.mem) (c.st0 s j U)) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q :=
    fun T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⟨L', b', hmc⟩ =>
      b4r impl c s R L' b' j Z U _ Q T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hmc (by omega) (k L' b')
  have hB : Box (A3 R c s Lk bk S j Z U qn) := ⟨hA⟩
  have hsl := hA.bd.sl
  have hpc := hA.pc; have hsp := hA.sp; have h5 := hA.r5; have h14 := hA.r14; have hfs := hA.fs; have hdf := hA.df
  have hx15 := hA.x15
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hA.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 : S.mem.readLE ((s.regs 4).toNat - 72) 8 = c.qv s S.mem := hA.v3.s328
  have r2 : S.mem.readLE ((s.regs 4).toNat - 240) 8 = 3 * c.vl := hA.v3.s168
  have r3 : S.mem.readLE ((s.regs 4).toNat - 256) 8 = 3 * c.vl := hA.v3.s152
  have r4' : S.mem.readLE ((s.regs 4).toNat + 8) 8 = c.vp := hsl.vp
  have r5 : S.mem.readLE ((s.regs 4).toNat - 272) 8 = c.vl / 2 - 1 := hA.bs.b1
  have r6 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = c.vc := hsl.vc
  have r7 : S.mem.readLE ((s.regs 4).toNat + 56) 8 = c.st := hsl.s4
  have r8 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = c.t0 := hsl.q0p
  have r9 : S.mem.readLE ((s.regs 4).toNat - 200) 8 = qn := hA.q3.s208
  have r10 : S.mem.readLE ((s.regs 4).toNat - 224) 8 = c.vl / 2 + 1 := hsl.q0c
  have hvp48 : c.vp + 8 * c.vl ≤ 2 ^ 48 := hpre.va.2.1
  have hvc40 : c.vc < 2 ^ 40 := hpre.vc40
  clear hA hcr hpre hsl k
  janus64_run [r1, r2, r3, r4', r5, r6, r7, r8, r9, r10] until [segAddr Extracted.program FvModexp.Amd64.Q.NatMul.fn]
  refine b4c impl hap R ns hns hcode hmul c s Lk bk S j Z U qn hB.h Q _ rfl ?sp ?r5 ?r14 hfs rfl hx15
    ?r0 ?r3 ?r1 ?r7 ?r6 ?r8 ?r9 (by unfold is4; janus_frame) (by janus64_simp) ?ra ?a1 ?a2 ?a3 kT
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r1 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r7 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r6 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r8 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r9 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case a1 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case a2 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case a3 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
