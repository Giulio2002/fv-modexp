import FvModexp.Proofs.Amd64.Exp.P2DTz
import FvModexp.Proofs.Amd64.Exp.P2DRun
import FvModexp.Proofs.Amd64.Nat.RshDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): after the `trailingZeroBits` loop (agent asm s69; twin of infra's arm64 `P2DTz.tzE`)

From `tzX` (`RAX = zp`, `R12 = tz`, `R15 = y[0]`): `MULQ` (`RDX:RAX = tz · y[0]`); overflow or `≥ logM` → `zero2`
(`R13 = zp`); else the spills `W1` (`0xa8 = st`, `0xc8 = logM`, `0xa0 = zc`, `0x98 = zl`, `0x60 = zp`, `0x58 = lo`),
`rsh(nil, x, tz)` with the return address `rshR` pushed at `sp - 8`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

/-- `nat.rsh`'s entry -/
abbrev rshE : Nat := 0x5e69c0
abbrev rshR : Nat := 0x5e91b7

theorem rsh_a : segAddr Extracted.program Rsh.fn = rshE := by decide

/-- the spills of the recursive path and the pushed return address -/
@[reducible] def W1 (M : Memory) (sp st lm zc zl zp lo : Nat) : Memory :=
  ((((((M.writeLE (sp + 0xa8) 8 st).writeLE (sp + 0xc8) 8 lm).writeLE (sp + 0xa0) 8 zc).writeLE (sp + 0x98) 8
    zl).writeLE (sp + 0x60) 8 zp).writeLE (sp + 0x58) 8 lo).writeLE (sp - 8) 8 rshR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **after the loop** (see the module doc) -/
theorem tzE {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp zp zl zc st xp xl xc lm tz y0 : Nat)
    (M : Memory) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0xd0 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 0xd8 true = true)
    (hz : zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ lm < 2 ^ 64 ∧ tz < 2 ^ 64 ∧ y0 < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 tzX) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = BitVec.ofNat 64 lm)
    (h12 : S.regs 12 = BitVec.ofNat 64 tz) (h15 : S.regs 15 = BitVec.ofNat 64 y0) (hmem : S.mem = M)
    (KZ : (tz * y0 / 2 ^ 64 ≠ 0 ∨ lm ≤ tz * y0 % 2 ^ 64) → ∀ S' : State, S'.rip = BitVec.ofNat 64 zero2 →
      S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 13 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = M →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KR : tz * y0 < 2 ^ 64 → tz * y0 < lm → ∀ S' : State, S'.rip = BitVec.ofNat 64 rshE →
      S'.regs 4 = BitVec.ofNat 64 (sp - 8) → S'.regs 0 = 0#64 → S'.regs 3 = 0#64 → S'.regs 1 = 0#64 →
      S'.regs 7 = BitVec.ofNat 64 xp → S'.regs 6 = BitVec.ofNat 64 xl → S'.regs 8 = BitVec.ofNat 64 xc →
      S'.regs 9 = BitVec.ofNat 64 tz → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase →
      S'.xmm 15 = S.xmm 15 → S'.df = S.df → S'.mem = W1 M sp st lm zc zl zp (tz * y0) →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have hm : (BitVec.ofNat 64 tz * BitVec.ofNat 64 y0).toNat = tz * y0 % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt z6, Nat.mod_eq_of_lt z7]
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x5 : S.regs 5 = r5 at KR
  generalize x14 : S.regs 14 = r14 at KZ KR
  generalize xf : S.fsBase = rf at KZ KR
  generalize xx : S.xmm 15 = rx at KZ KR
  generalize xd : S.df = rd at KZ KR
  subst hmem
  janus64_run [hm, e4] until [0x5e916a, 0x5e69c0]
  · have hlo : tz * y0 < 2 ^ 64 := by
      have := Nat.div_add_mod (tz * y0) (2 ^ 64)
      rw [(by janus_assumption : tz * y0 / 18446744073709551616 = 0)] at this; omega
    refine KR hlo hbr _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus64_simp; done) | (janus64_simp; first | exact xf | exact xx | exact xd | exact x5 |
      exact x14)
  · exact KZ (Or.inr (by omega)) _ rfl (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp; exact xf) (by janus64_simp) (by janus64_simp)
      rfl
  · exact KZ (Or.inl hbr) _ rfl (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp; exact xf) (by janus64_simp) (by janus64_simp)
      rfl
