import FvModexp.Proofs.Amd64.Exp.EvJ11

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the run `smR` → `nat.modularInverseModPowerOfTwo`'s entry (asm s62; twin of infra's arm64
`EvMiR`)

`smR`: spill `z3 = (RAX, RBX, RCX)` to `0x100/0x90/0x98`; `m1` (`0x118/0xc8/0xd0`) → `RAX/RBX/RCX`, `stk` (`0x198`) →
`RDI`, `m2` (`0x110/0xb8/0xc0`) → `RSI/R8/R9`, `n` (`0xb0`) → `R10`; `CALL` (push `miR`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `smR` → `modularInverseModPowerOfTwo`'s entry -/
theorem runMi {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st p1 l1 c1 q l2 c2 n p3 l3 c3 : Nat)
    (M : Memory) (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h118 : M.readLE (sp + 0x118) 8 = p1) (hc8 : M.readLE (sp + 0xc8) 8 = l1) (hd0 : M.readLE (sp + 0xd0) 8 = c1)
    (h198 : M.readLE (sp + 0x198) 8 = st) (h110 : M.readLE (sp + 0x110) 8 = q) (hb8 : M.readLE (sp + 0xb8) 8 = l2)
    (hc0 : M.readLE (sp + 0xc0) 8 = c2) (hb0 : M.readLE (sp + 0xb0) 8 = n)
    (hp : p3 < 2 ^ 64) (hl : l3 < 2 ^ 64) (hc : c3 < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 smR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 p3) (h3 : S.regs 3 = BitVec.ofNat 64 l3) (h1 : S.regs 1 = BitVec.ofNat 64 c3)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 miE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp), (sp + 0x90, sp + 0xa0), (sp + 0x100, sp + 0x108)] →
      M'.regions = M.regions → M'.readLE (sp - 8) 8 = miR →
      M'.readLE (sp + 0x100) 8 = p3 → M'.readLE (sp + 0x90) 8 = l3 → M'.readLE (sp + 0x98) 8 = c3 →
      S'.regs 0 = BitVec.ofNat 64 p1 → S'.regs 3 = BitVec.ofNat 64 l1 → S'.regs 1 = BitVec.ofNat 64 c1 →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 q → S'.regs 8 = BitVec.ofNat 64 l2 →
      S'.regs 9 = BitVec.ofNat 64 c2 → S'.regs 10 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  janus64_run [h118, hc8, hd0, h198, h110, hb8, hc0, hb0, e4] until [miE]
  refine K _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x90, sp + 0xa0)) (by simp) (by simp only; omega)
          (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x100, sp + 0x108)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | (janus64_simp; first | exact h0 | exact h1 | exact h3) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h0, h1, h3]
  all_goals first | omega | rfl | exact xf | exact xx | skip

end FvModexp.Amd64.ExpEven
