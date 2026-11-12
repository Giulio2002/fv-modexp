import FvModexp.Proofs.Arm64.Exp.EvJ11

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the run `smR` → `nat.modularInverseModPowerOfTwo`'s entry (agent infra)

`runMi`: spill the `subMod2N` result `z3` (`X0..X2`) to `264/152/160`, `R0..R2 = m1` (`288/208/216`), `R3 = stk`
(`368`), `R4..R6 = m2` (`280/192/200`), `R7 = n` (`184`), `CALL nat.modularInverseModPowerOfTwo` (return `miR`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `smR` → `nat.modularInverseModPowerOfTwo`'s entry -/
theorem runMi {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st p1 l1 c1 q l2 c2 n p3 l3 c3 : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 136) 312 true = true)
    (h288 : M.readLE (sp + 288) 8 = p1) (h208 : M.readLE (sp + 208) 8 = l1) (h216 : M.readLE (sp + 216) 8 = c1)
    (h368 : M.readLE (sp + 368) 8 = st) (h280 : M.readLE (sp + 280) 8 = q) (h192 : M.readLE (sp + 192) 8 = l2)
    (h200 : M.readLE (sp + 200) 8 = c2) (h184 : M.readLE (sp + 184) 8 = n)
    (hp : p3 < 2 ^ 64) (hl : l3 < 2 ^ 64) (hc : c3 < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 smR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 p3) (h1 : S.regs 1 = BitVec.ofNat 64 l3) (h2 : S.regs 2 = BitVec.ofNat 64 c3)
    (KN : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 1797104 → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 p1 → S'.regs 1 = BitVec.ofNat 64 l1 → S'.regs 2 = BitVec.ofNat 64 c1 →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 q → S'.regs 5 = BitVec.ofNat 64 l2 →
      S'.regs 6 = BitVec.ofNat 64 c2 → S'.regs 7 = BitVec.ofNat 64 n →
      S'.regs 30 = BitVec.ofNat 64 miR →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 152, sp + 168), (sp + 264, sp + 272)] → M'.regions = M.regions →
      M'.readLE (sp + 264) 8 = p3 → M'.readLE (sp + 152) 8 = l3 → M'.readLE (sp + 160) 8 = c3 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  janus_run [hal, hacc] until [1797104]
  refine KN _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 152, sp + 168)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 264, sp + 272)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte,
    Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h288, h208, h216, h368, h280, h192, h200, h184]
  all_goals first | omega | skip
  all_goals first | (rw [← eS, hsp]; done) | skip

end FvModexp.Arm64.ExpEven
