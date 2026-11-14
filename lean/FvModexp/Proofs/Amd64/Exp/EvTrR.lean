import FvModexp.Proofs.Amd64.Exp.EvJ12
import FvModexp.Proofs.Amd64.Exp.EvTrD

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the runs `mul1R` → `nat.trunc` and `mul2R` → `nat.add` (asm s63)

`runTr` (`mul1R`): `RDI/RSI/R8 := RAX/RBX/RCX` (`x = t`, `z = t` stays in `RAX/RBX/RCX`), `R9 := n` (`0xb0`),
`CALL nat.trunc` (pushes `trR`). `runAdd` (`mul2R`): `RDI/RSI/R8 := z` (`0x108/0xa0/0xa8`), `R9/R10/R11 := RAX/RBX/RCX`
(`u`), `RAX/RBX/RCX := z`, `CALL nat.add` (pushes `addR`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

theorem trunc_aE : segAddr Extracted.program Trunc.fn = 6188320 := by decide
theorem add_aE : segAddr Extracted.program NatAdd.fn = 6182240 := by decide

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mul1R` → `nat.trunc`'s entry -/
theorem runTr {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp n : Nat)
    (M : Memory) (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hb0 : M.readLE (sp + 0xb0) 8 = n)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mul1R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 6188320 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp)] →
      M'.regions = M.regions → M'.readLE (sp - 8) 8 = trR →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 →
      S'.regs 7 = S.regs 0 → S'.regs 6 = S.regs 3 → S'.regs 8 = S.regs 1 → S'.regs 9 = BitVec.ofNat 64 n →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  janus64_run [hb0, e4] until [6188320]
  refine K _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | exact xf | exact xx | skip

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mul2R` → `nat.add`'s entry -/
theorem runAdd {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp pZ lw cZ : Nat)
    (M : Memory) (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h108 : M.readLE (sp + 0x108) 8 = pZ) (ha0 : M.readLE (sp + 0xa0) 8 = lw) (ha8 : M.readLE (sp + 0xa8) 8 = cZ)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mul2R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 6182240 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp)] →
      M'.regions = M.regions → M'.readLE (sp - 8) 8 = addR →
      S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 3 = BitVec.ofNat 64 lw → S'.regs 1 = BitVec.ofNat 64 cZ →
      S'.regs 7 = BitVec.ofNat 64 pZ → S'.regs 6 = BitVec.ofNat 64 lw → S'.regs 8 = BitVec.ofNat 64 cZ →
      S'.regs 9 = S.regs 0 → S'.regs 10 = S.regs 3 → S'.regs 11 = S.regs 1 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  janus64_run [h108, ha0, ha8, e4] until [6182240]
  refine K _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | exact xf | exact xx | skip

end FvModexp.Amd64.ExpEven
