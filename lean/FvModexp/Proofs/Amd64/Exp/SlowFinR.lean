import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the run `ex` → `RET` (agent asm s74; nat.go:787 `return z.norm()`, nat.go:51-54)

At `ex` (`fnE + 0x7c5`) `z = (AX, R10, R8)` is normalised, so the `norm` loop makes one test (`len z = 0`: `JLE`;
else `z[len z - 1] ≠ 0`: `JE` not taken); `CMPQ R10, R8; JA panicBounds` not taken (`len ≤ cap`); `BX = R10`,
`CX = R8`, `ADDQ $0x1a8, SP; POPQ BP; RET`. No stores.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the state after `RET` -/
@[reducible] def FP (sp g fs bp p l c : Nat) (M : Memory) (s' : State) : Prop :=
  s'.regs 4 = BitVec.ofNat 64 (sp + 0x1b8) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = BitVec.ofNat 64 g ∧
    s'.fsBase.toNat = fs ∧ s'.xmm 15 = 0 ∧ s'.df = false ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧ s'.mem = M

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem runFin {impl : List Amd64.Segment} (S : State) (sp g fs bp r p l c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 ex) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h10 : S.regs 10 = BitVec.ofNat 64 l) (h8 : S.regs 8 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hp : p < 2 ^ 64) (hlc : l ≤ c) (hc : c < 2 ^ 64)
    (hn : 0 < l → M.readLE (p + l * 8 - 8) 8 ≠ 0) (hza : 0 < l → M.accessible (p + l * 8 - 8) 8 false = true)
    (hpl : p + l * 8 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 0x1a8) 16 false = true) (hbp : M.readLE (sp + 0x1a8) 8 = bp)
    (hr : M.readLE (sp + 0x1b0) 8 = r) (hr47 : r < 2 ^ 47) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FP sp g fs bp p l c M) := by
  have hl : l < 2 ^ 64 := by omega
  subst hmem
  rcases Nat.eq_zero_or_pos l with l0 | l0
  · subst l0
    janus64_run [hacc, hbp, hr, BitVec.msb_eq_decide]
    refine ⟨?_, ?_, ?_, hfs, hx15, by first | rfl | (show S.df = false; exact hdf), ?_, ?_, ?_, rfl⟩
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first
      | exact h14
      | exact h0
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | rfl
  · have hn' := hn l0
    have hza' := hza l0
    have e1 : l * 8 % 18446744073709551616 = l * 8 := Nat.mod_eq_of_lt (by omega)
    have e2 : (p + l * 8) % 18446744073709551616 = p + l * 8 := Nat.mod_eq_of_lt (by omega)
    have e3 : (18446744073709551608 + (p + l * 8)) % 18446744073709551616 = p + l * 8 - 8 := by omega
    janus64_run [hacc, hbp, hr, hn', hza', e1, e2, e3, BitVec.msb_eq_decide]
    refine ⟨?_, ?_, ?_, hfs, hx15, by first | rfl | (show S.df = false; exact hdf), ?_, ?_, ?_, rfl⟩
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first
      | exact h14
      | exact h0
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | rfl

end FvModexp.Amd64.ExpSlow
