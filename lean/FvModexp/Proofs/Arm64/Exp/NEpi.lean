import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64): the shared epilogue after a callee (`rem`, `expNNSlow`, `expNNOdd`, `expNNPowerOfTwo`)

From a return point: the result `X0..X2` is stored to `SP' + 176..200`, the defer flag byte `SP' + 126` is tested (0:
no deferred call — the stack-given path), the result reloaded, FP/LR reloaded, `ADD $256`, `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- the return points of the four callees (rem, slow, odd, power of two) -/
@[reducible] def RetPt (r : Nat) : Prop := r = 1787296 ∨ r = 1787596 ∨ r = 1787680 ∨ r = 1788032

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem epi0 (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (F : State → Prop) (sp f29 r : Nat) (M : Memory) (hr : RetPt r)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 1048) 216 true = true)
    (h29v : M.readLE (sp + 1048) 8 = f29) (h30v : M.readLE (sp + 1056) 8 = ret0) (hfl : M.readLE (sp + 1182) 1 = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 r) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (hmem : S.mem = M)
    (hK : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 1312) → s'.regs 29 = BitVec.ofNat 64 f29 →
      s'.regs 0 = S.regs 0 → s'.regs 1 = S.regs 1 → s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 →
      s'.regs 28 = S.regs 28 → MemFrame M s'.mem [(sp + 1232, sp + 1256)] → s'.mem.regions = M.regions → F s') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have es : BitVec.ofNat 64 (sp + 1056) - 8#64 = BitVec.ofNat 64 (sp + 1048) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 1056) + 256#64 = BitVec.ofNat 64 (sp + 1312) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rcases hr with rfl | rfl | rfl | rfl
  all_goals
    janus_run [es, es2, h29v, h30v, hfl]
    refine hK _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | rfl | (janus_simp; done) | skip
    all_goals
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _

end FvModexp.Arm64.ExpN
