import FvModexp.Proofs.Amd64.Exp.EvJ10

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the run `mvJ` → `subMod2N`'s entry (asm s61; the run part of infra's arm64 `EvSm`)

nat.go `z1 = z1.subMod2N(z1, z2, n)`: `n` (`0xb0`) to the stack argument `[sp]`; `z1` (`0x100/0x90/0x98`) to both
the receiver `RAX/RBX/RCX` and the first argument `RDI/RSI/R8`; `z2` (`RAX/RSI/RCX` at `mvJ`) to `R9/R10/R11`;
`CALL subMod2N` (entry `0x5ed840`, return `smR`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `nat.subMod2N`'s entry -/
abbrev smE : Nat := 6215840

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mvJ` → `subMod2N`'s entry -/
theorem runSm {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp pz lz cz n pw lw cw : Nat)
    (M : Memory) (hacc2 : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h100 : M.readLE (sp + 0x100) 8 = pz) (h90 : M.readLE (sp + 0x90) 8 = lz) (h98 : M.readLE (sp + 0x98) 8 = cz)
    (hb0 : M.readLE (sp + 0xb0) 8 = n)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 mvJ) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h1 : S.regs 1 = BitVec.ofNat 64 cw) (h6 : S.regs 6 = BitVec.ofNat 64 lw)
    (K : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 smE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 8)] → M'.regions = M.regions → M'.readLE (sp - 8) 8 = smR →
      M'.readLE sp 8 = n →
      S'.regs 0 = BitVec.ofNat 64 pz → S'.regs 3 = BitVec.ofNat 64 lz → S'.regs 1 = BitVec.ofNat 64 cz →
      S'.regs 7 = BitVec.ofNat 64 pz → S'.regs 6 = BitVec.ofNat 64 lz → S'.regs 8 = BitVec.ofNat 64 cz →
      S'.regs 9 = BitVec.ofNat 64 pw → S'.regs 10 = BitVec.ofNat 64 lw → S'.regs 11 = BitVec.ofNat 64 cw →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have bn : n < 2 ^ 64 := hb0 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x5 : S.regs 5 = r5 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  janus64_run [h100, h90, h98, hb0, e4] until [smE]
  refine K _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat
      refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 8)) (by simp) (by simp only; omega) (by simp only; omega)
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | (janus64_simp; first | exact h0 | exact h1 | exact h6) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | exact xf | exact xx | skip

end FvModexp.Amd64.ExpEven
