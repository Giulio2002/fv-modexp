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


/-! ## The epilogue as a continuation (flag-generic chain, s26)

The downstream chain (from `J5` / `rem`'s entry) is shared by the stack-given path (defer flag byte `SP' + 126` = 0)
and the `stk == nil` path (flag 1, closure record `SP' + 216/224`, `SP' + 240`, byte `SP' + 127`). It carries the
frame slots of the flag and the record unchanged (`SlotEq M M0 sp`: equal to those of the reference memory `M0`, the
memory at `J5`) and ends in an abstract epilogue `EpiK`: from a callee return point, given the function's post `P` at
every state that only adds the result stores. `epiK0`: the flag-0 epilogue (`epi0`) is one. -/

/-- the defer flag bytes `SP' + 126/127` and the closure record words `SP' + 216, 224, 240` -/
@[reducible] def Slot (sp a k : Nat) : Prop :=
  (sp + 1182 ≤ a ∧ a + k ≤ sp + 1184) ∨ (sp + 1272 ≤ a ∧ a + k ≤ sp + 1288) ∨ (sp + 1296 ≤ a ∧ a + k ≤ sp + 1304)

/-- the slots of `M` are those of `M0` -/
def SlotEq (M M0 : Memory) (sp : Nat) : Prop := ∀ a k, Slot sp a k → M.readLE a k = M0.readLE a k

theorem SlotEq.refl (M : Memory) (sp : Nat) : SlotEq M M sp := fun _ _ _ => rfl

theorem SlotEq.of_rd {M M' M0 : Memory} {sp : Nat} (h : SlotEq M M0 sp)
    (hk : ∀ a k, Slot sp a k → M'.readLE a k = M.readLE a k) : SlotEq M' M0 sp :=
  fun a k hs => (hk a k hs).trans (h a k hs)

theorem SlotEq.of_frame {M M' M0 : Memory} {sp : Nat} {ws : List (Nat × Nat)} (h : SlotEq M M0 sp)
    (hF : MemFrame M M' ws) (ho : ∀ a k, Slot sp a k → Outside a k ws) : SlotEq M' M0 sp :=
  h.of_rd fun a k hs => hF.readLE a k (ho a k hs)

/-- the epilogue from a callee return point `r` (`SP' = sp + 1056`): given the post `P` at every state that differs
from the return-point state only by the result stores `SP' + 176..200`, the function returns with `F` -/
def EpiK (impl : List Segment) (ret0 : Nat) (F : State → Prop) (sp f29 : Nat) (r18 r28 : BitVec 64) (M0 : Memory)
    (P : State → Prop) : Prop :=
  ∀ (r : Nat) (S : State), RetPt r → S.pc = BitVec.ofNat 64 r → S.sp = BitVec.ofNat 64 (sp + 1056) →
    S.regs 18 = r18 → S.regs 28 = r28 →
    S.mem.accessible (sp + 1048) 216 true = true → S.mem.readLE (sp + 1048) 8 = f29 →
    S.mem.readLE (sp + 1056) 8 = ret0 → SlotEq S.mem M0 sp →
    (∀ s'' : State, MemFrame S.mem s''.mem [(sp + 1232, sp + 1256)] → s''.regs 0 = S.regs 0 →
      s''.regs 1 = S.regs 1 → s''.regs 2 = S.regs 2 → P s'') →
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F)

/-- the stack-given epilogue (flag 0) -/
theorem epiK0 (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    (sp f29 : Nat) (r18 r28 : BitVec 64) (M0 : Memory) (P : State → Prop)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48) (hfl : M0.readLE (sp + 1182) 1 = 0)
    (hK' : ∀ s'' : State, s''.sp = BitVec.ofNat 64 (sp + 1312) → s''.regs 29 = BitVec.ofNat 64 f29 →
      s''.regs 18 = r18 → s''.regs 28 = r28 → P s'' → F s'') :
    EpiK impl ret0 F sp f29 r18 r28 M0 P := by
  intro r S hr hpc hsp h18 h28 hacc h29v h30v hsl hP
  exact epi0 impl ret0 hret F sp f29 r S.mem hr hal hsp1 hsp2 hacc h29v h30v
    ((hsl _ _ (Or.inl ⟨Nat.le_refl _, by omega⟩)).trans hfl) S hpc hsp rfl
    fun s'' f1 f2 f3 f4 f5 f6 f7 f8 _ => hK' s'' f1 f2 (f6.trans h18) (f7.trans h28) (hP s'' f8 f3 f4 f5)

end FvModexp.Arm64.ExpN
