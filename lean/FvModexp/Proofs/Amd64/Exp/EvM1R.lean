import FvModexp.Proofs.Amd64.Exp.EvJ12

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the runs `miR` → `nat.mul` and `trR` → `nat.mul` (asm s63)

`runMul1` (`miR`): `[sp, sp + 24) := m2inv` (`RAX/RBX/RCX`, `y` on the stack), `z2` (`0xf8/0x80/0x88`) → `RAX/RBX/RCX`,
`stk` (`0x198`) → `RDI`, `z3` (`0x100/0x90/0x98`) → `RSI/R8/R9`, `CALL nat.mul` (pushes `mul1R`).
`runMul2` (`trR`): `[sp, sp + 24) := m2` (`0x110/0xb8/0xc0`), `RDI = stk`, `RSI/R8/R9 := RAX/RBX/RCX` (`t mod 2^n`),
`z3` (`0x100/0x90/0x98`) → `RAX/RBX/RCX`, `CALL nat.mul` (pushes `mul2R`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `miR` → `nat.mul`'s entry -/
theorem runMul1 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st pw lw cw p3 l3 c3 p4 l4 c4 : Nat)
    (M : Memory) (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hf8 : M.readLE (sp + 0xf8) 8 = pw) (h80 : M.readLE (sp + 0x80) 8 = lw) (h88 : M.readLE (sp + 0x88) 8 = cw)
    (h198 : M.readLE (sp + 0x198) 8 = st) (h100 : M.readLE (sp + 0x100) 8 = p3) (h90 : M.readLE (sp + 0x90) 8 = l3)
    (h98 : M.readLE (sp + 0x98) 8 = c3)
    (hp : p4 < 2 ^ 64) (hl : l4 < 2 ^ 64) (hc : c4 < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 miR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 p4) (h3 : S.regs 3 = BitVec.ofNat 64 l4) (h1 : S.regs 1 = BitVec.ofNat 64 c4)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 6228032 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 0x18)] →
      M'.regions = M.regions → M'.readLE (sp - 8) 8 = mul1R →
      M'.readLE sp 8 = p4 → M'.readLE (sp + 8) 8 = l4 → M'.readLE (sp + 0x10) 8 = c4 →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 3 = BitVec.ofNat 64 lw → S'.regs 1 = BitVec.ofNat 64 cw →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 p3 → S'.regs 8 = BitVec.ofNat 64 l3 →
      S'.regs 9 = BitVec.ofNat 64 c3 →
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
  janus64_run [hf8, h80, h88, h198, h100, h90, h98, e4] until [6228032]
  refine K _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | (janus64_simp; first | exact h0 | exact h1 | exact h3) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h0, h1, h3]
  all_goals first | omega | rfl | exact xf | exact xx | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `trR` → `nat.mul`'s entry -/
theorem runMul2 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st q l2 c2 p3 l3 c3 pt lu ct : Nat)
    (M : Memory) (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h110 : M.readLE (sp + 0x110) 8 = q) (hb8 : M.readLE (sp + 0xb8) 8 = l2) (hc0 : M.readLE (sp + 0xc0) 8 = c2)
    (h198 : M.readLE (sp + 0x198) 8 = st) (h100 : M.readLE (sp + 0x100) 8 = p3) (h90 : M.readLE (sp + 0x90) 8 = l3)
    (h98 : M.readLE (sp + 0x98) 8 = c3)
    (hq : q < 2 ^ 64) (hl : l2 < 2 ^ 64) (hc : c2 < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 trR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pt) (h3 : S.regs 3 = BitVec.ofNat 64 lu) (h1 : S.regs 1 = BitVec.ofNat 64 ct)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 6228032 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 0x18)] →
      M'.regions = M.regions → M'.readLE (sp - 8) 8 = mul2R →
      M'.readLE sp 8 = q → M'.readLE (sp + 8) 8 = l2 → M'.readLE (sp + 0x10) 8 = c2 →
      S'.regs 0 = BitVec.ofNat 64 p3 → S'.regs 3 = BitVec.ofNat 64 l3 → S'.regs 1 = BitVec.ofNat 64 c3 →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 pt → S'.regs 8 = BitVec.ofNat 64 lu →
      S'.regs 9 = BitVec.ofNat 64 ct →
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
  janus64_run [h110, hb8, hc0, h198, h100, h90, h98, e4] until [6228032]
  refine K _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | (janus64_simp; first | exact h0 | exact h1 | exact h3) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h0, h1, h3]
  all_goals first | omega | rfl | exact xf | exact xx | skip

end FvModexp.Amd64.ExpEven
