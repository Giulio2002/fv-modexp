import FvModexp.Proofs.Arm64.Exp.W4Defs
import FvModexp.Proofs.Arm64.Exp.DeferW
import FvModexp.Proofs.Common.ExpNorm

/-!
# window-4 (arm64), the end: `return zz.norm()` (nat.go:1490) with the deferred `stk.restore`

From the join point (entry + 0xbb4: `zz` in `X3..X5` after the final reduction) the inline `norm` loop, the named-result
stores, the call of the open-coded defer closure (`DeferW.sum`) and the return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

/-- the norm loop test `CMP $0, R4` -/
abbrev njoin : Nat := segAddr LibExp.program fn + 0xbb4
/-- after the norm loop: `CMP R5, R4` -/
abbrev tailPc : Nat := segAddr LibExp.program fn + 0xbc8

/-- what the end guarantees (memory relative to the memory `M` at the join point) -/
@[reducible] def FinPost (sp g st n0 p l c : Nat) (r18 r29 : BitVec 64) (M : Memory) (s' : State) : Prop :=
  s'.sp = BitVec.ofNat 64 (sp + 928) ∧ s'.regs 18 = r18 ∧ s'.regs 28 = BitVec.ofNat 64 g ∧ s'.regs 29 = r29 ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧
    MemFrame M s'.mem [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)]

/-- the static facts of the end -/
@[reducible] def FinEnv (sp g st n0 : Nat) (r29 : BitVec 64) (ret : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ 4288 ≤ sp ∧ sp + 1040 ≤ 2 ^ 48 ∧ M.accessible (sp - 4288) (4288 + 1040) true = true ∧
    g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + 4288 < sp ∧
    Apart (g + 16) 8 (sp - 4288) (4288 + 1040) ∧
    M.readLE (sp + 912) 8 = sp + 840 ∧ M.readLE (sp + 840) 8 = segAddr LibExp.program DeferW.fnW4 ∧
    M.readLE (sp + 848) 8 = st ∧ M.readLE (sp + 856) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 4288) (4288 + 1040) ∧ Apart st 24 (g + 16) 8 ∧
    M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem tail (impl : List Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (hret : RetAddr (LibExp.program.link impl) ret)
    (S : State) (sp g st n0 p l c : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 tailPc) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 p) (h4 : S.regs 4 = BitVec.ofNat 64 l) (h5 : S.regs 5 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hlc : l ≤ c) (hc : c < 2 ^ 40) (he : FinEnv sp g st n0 r29 ret M) :
    Reaches ((LibExp.program.link impl).withExit ret) S (IsReturn (FinPost sp g st n0 p l c r18 r29 M)) := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r912, r840, r848, r856, hst1, hst2, hn0, hstw, hstg, rfp, rlr⟩ := he
  have hD := DeferW.sum impl hap DeferW.fnW4 (by simp [DeferW.fnW4])
  have eD : segAddr LibExp.program DeferW.fnW4 = 1801824 := by decide
  rw [eD] at hD r840
  janus_run [r912, r840, r848, r856, rfp, rlr] calls [hD]
  refine ⟨?sp, ?_, ?_, ?_, ?r0, ?_, ?_, ?st, ?fr⟩
  case sp => dsimp only; apply BitVec.eq_of_toNat_eq; simp; try omega
  case r0 => janus_simp; try (apply BitVec.eq_of_toNat_eq; simp)
  case st => dsimp only; assumption
  case fr => janus_frame
  all_goals janus_simp

end FvModexp.Arm64.W4Loop
