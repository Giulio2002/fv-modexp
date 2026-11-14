import FvModexp.Proofs.Amd64.Exp.P2DRecR
import FvModexp.Proofs.Amd64.Nat.LshDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `recR` → `lsh` entry and the final epilogue (agent asm s70; twins of infra's
arm64 `P2DLshR.runL` / `epiL`)

`runL`: `x = z = ` the recursive result (`RAX/RBX/RCX` → `RDI/RSI/R8`), `R9 = [sp + 0x58] = lo`, `[sp - 8] := lshR`.
`epiL`: at `lshR`, `ADDQ $0x68, SP; POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

/-- `nat.lsh`'s entry -/
abbrev lshE : Nat := 0x5e6620
abbrev lshR : Nat := 0x5e9228

theorem lsh_a : segAddr Extracted.program Lsh.fn = lshE := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the run `recR` → `lshE` -/
theorem runL {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp lo : Nat) (M : Memory)
    (hsp1 : 8 ≤ sp) (hsp2 : sp + 0xd0 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 0xd8 true = true)
    (h58 : M.readLE (sp + 0x58) 8 = lo)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 recR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 lshE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 →
      S'.regs 7 = S.regs 0 → S'.regs 6 = S.regs 3 → S'.regs 8 = S.regs 1 → S'.regs 9 = BitVec.ofNat 64 lo →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.mem = M.writeLE (sp - 8) 8 lshR → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x0 : S.regs 0 = r0 at K
  generalize x3 : S.regs 3 = r3 at K
  generalize x1 : S.regs 1 = r1 at K
  generalize x14 : S.regs 14 = r14 at K
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [h58, e4] until [0x5e6620]
  refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact xf)

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {sp bp : Nat} {S : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the epilogue after `lsh` -/
theorem epiL (hpc : S.rip = BitVec.ofNat 64 lshR)
    (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hsp : sp + 0x78 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hra : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 0 → s'.regs 3 = S.regs 3 → s'.regs 1 = S.regs 1 →
      s'.mem = S.mem → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e := sp78 hsp
  janus64_run [hbp, hra]
  exact K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl

end

end FvModexp.Amd64.P2D
