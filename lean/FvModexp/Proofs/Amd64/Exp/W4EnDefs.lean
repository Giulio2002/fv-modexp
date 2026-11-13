import FvModexp.Proofs.Amd64.Exp.CallW
import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Nat.StackNatCall
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# window-4 entry (amd64): pcs and the frame facts after the prologue (agent expmc s57; twin of `Arm64.W4EnDefs`)

`nat.expNNOddMontgomeryWindowSize4` (fn = 0x5eb060 = 6205536) from its entry to `xnE` (fn+0x216): stack-guard check,
`PUSHQ BP`, `SUBQ $0x380` (frame `sp = RSP - 0x388`, saved `BP` at `sp + 0x380`, return address at `sp + 0x388`),
argument spills (`AX → 0x3c0`, `SI → 0x3e0`, then `DI, R9, R8, SI, CX, AX` → `0x3d8, 0x3f0, 0x3e8, 0x3e0, 0x3d0,
0x3c0`), the `defer stk.restore(stk.save())` record (`[0x340]` = closure 0x5ec3c0, `[0x348]` = st, `[0x350]` = old len,
`[0x378]` = sp + 0x340) and the INLINE `stk.reserve(23·n)` (nat.go:333-337 = `slices.Grow` + header update):
`growslice`/`memclrNoHeapPointers` when the array is too small, the header stores with the write barrier,
`len := len + rnd(23n)`. Stack arguments: `y = [0x390, 0x3a8)`, `m = [0x3a8, 0x3c0)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4En

/-- the function's entry -/
abbrev fnE : Nat := 6205536
/-- the join of `slices.Grow` (fn+0x1dc, `MOVQ R12, 8(DI)`) -/
abbrev enJ : Nat := 6206012
/-- return of `growslice` (fn+0x133) -/
abbrev grRet : Nat := 6205843
/-- return of `memclrNoHeapPointers` (fn+0x167) -/
abbrev mcRet : Nat := 6205895
/-- return of `gcWriteBarrier2` (fn+0x1fc) -/
abbrev wbRet : Nat := 6206044
/-- the pointer store `MOVQ R11, (DI)` (both write-barrier branches, fn+0x206) -/
abbrev enS : Nat := 6206054
/-- after the inline `stk.reserve` (fn+0x216) = `W4Pro.xnE` -/
abbrev xnE : Nat := 6206070
/-- `runtime.growslice` / `memclrNoHeapPointers` / `gcWriteBarrier2` (contract addresses of the extraction) -/
abbrev grE : Nat := 4740128
abbrev mcE : Nat := 4762336
abbrev wbE : Nat := 4761248
/-- the `big.Word` type descriptor -/
abbrev wTy : Nat := 7233184

theorem grE_eq : Extracted.program.contractAddr "runtime.growslice" = grE := by decide
theorem mcE_eq : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = mcE := by decide
theorem wbE_eq : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbE := by decide
theorem wTy_eq : StackNat.wT = wTy := rfl

/-- the frame slots after the prologue (saved `BP`, return address, defer record, argument spills, stack arguments) -/
@[reducible] def ESl (M : Memory) (sp st bp r zp zc xp xl xc yp ylen mp n mc len0 : Nat) : Prop :=
  M.readLE (sp + 0x380) 8 = bp ∧ M.readLE (sp + 0x388) 8 = r ∧ M.readLE (sp + 0x378) 8 = sp + 0x340 ∧
  M.readLE (sp + 0x340) 8 = 6210496 ∧ M.readLE (sp + 0x348) 8 = st ∧ M.readLE (sp + 0x350) 8 = len0 ∧
  M.readLE (sp + 0x3c0) 8 = zp ∧ M.readLE (sp + 0x3d0) 8 = zc ∧ M.readLE (sp + 0x3d8) 8 = st ∧
  M.readLE (sp + 0x3e0) 8 = xp ∧ M.readLE (sp + 0x3e8) 8 = xl ∧ M.readLE (sp + 0x3f0) 8 = xc ∧
  M.readLE (sp + 0x390) 8 = yp ∧ M.readLE (sp + 0x398) 8 = ylen ∧ M.readLE (sp + 0x3a8) 8 = mp ∧
  M.readLE (sp + 0x3b0) 8 = n ∧ M.readLE (sp + 0x3b8) 8 = mc

/-- the slots `ESl` names lie in `[sp + 0x340, sp + 0x358) ∪ [sp + 0x378, sp + 0x3f8)` -/
theorem ESl.keep {M1 M3 : Memory} {sp st bp r zp zc xp xl xc yp ylen mp n mc len0 : Nat}
    (h : ESl M1 sp st bp r zp zc xp xl xc yp ylen mp n mc len0)
    (hk : ∀ a, (sp + 0x340 ≤ a ∧ a + 8 ≤ sp + 0x358 ∨ sp + 0x378 ≤ a ∧ a + 8 ≤ sp + 0x3f8) →
      M3.readLE a 8 = M1.readLE a 8) : ESl M3 sp st bp r zp zc xp xl xc yp ylen mp n mc len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := h
  exact ⟨by rw [hk _ (by omega)]; exact a1, by rw [hk _ (by omega)]; exact a2, by rw [hk _ (by omega)]; exact a3,
    by rw [hk _ (by omega)]; exact a4, by rw [hk _ (by omega)]; exact a5, by rw [hk _ (by omega)]; exact a6,
    by rw [hk _ (by omega)]; exact a7, by rw [hk _ (by omega)]; exact a8, by rw [hk _ (by omega)]; exact a9,
    by rw [hk _ (by omega)]; exact a10, by rw [hk _ (by omega)]; exact a11, by rw [hk _ (by omega)]; exact a12,
    by rw [hk _ (by omega)]; exact a13, by rw [hk _ (by omega)]; exact a14, by rw [hk _ (by omega)]; exact a15,
    by rw [hk _ (by omega)]; exact a16, by rw [hk _ (by omega)]; exact a17⟩

/-- the call environment of the entry segment (entry state `s`, `RSP = sp + 0x388`, window `[sp - 8 - K, sp + 0x3f8)`
= the callee stacks, the frame, the saved `BP`, the return address, the stack arguments and the register spill area) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (s : State) : Prop :=
  s.regs 4 = BitVec.ofNat 64 (sp + 0x388) ∧ s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧
  s.xmm 15 = 0 ∧ s.df = false ∧ sp % 8 = 0 ∧ 41512 ≤ K ∧ K ≤ 2 ^ 20 ∧
  CallW.CEnv R L g fs (sp - 8) K 0x400 s.mem ∧ RunIface.Serves R

theorem rnd23 (n : Nat) (hn : n ≤ 128) :
    (BitVec.ofNat 64 n * 23#64 + 3#64) &&& BitVec.ofNat 64 18446744073709551612 =
      BitVec.ofNat 64 (StackNat.rnd (23 * n)) := by
  have e : BitVec.ofNat 64 n * 23#64 = BitVec.ofNat 64 (23 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]; omega
  have := StackNat.rnd_bv (BitVec.ofNat 64 (23 * n))
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 23 * n < 2 ^ 64 by omega)]; omega)
  rw [e]; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 23 * n < 2 ^ 64 by omega)] at this

/-- the sign of `nr - (cap - len)` (the `TEST R10, R10; JLE` of `slices.Grow`) -/
theorem sub3_msb (a r c : Nat) (ha : a < 2 ^ 60) (hr : r < 2 ^ 60) (hc : c < 2 ^ 60) (hac : a ≤ c) :
    (BitVec.ofNat 64 r - (BitVec.ofNat 64 c - BitVec.ofNat 64 a)).msb = decide (a + r < c) := by
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  apply decide_eq_decide.2
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega)]
  constructor <;> intro h <;> omega

/-- the zero flag of `nr - (cap - len)` -/
theorem sub3_z (a r c : Nat) (ha : a < 2 ^ 60) (hr : r < 2 ^ 60) (hc : c < 2 ^ 60) (hac : a ≤ c) :
    ((18446744073709551616 - (18446744073709551616 - a + c) % 18446744073709551616 + r) % 18446744073709551616 = 0) =
      (a + r = c) := by
  apply propext; constructor <;> intro h <;> omega

theorem rnd23_le (n : Nat) : StackNat.rnd (23 * n) ≤ 23 * n + 3 := by simp only [StackNat.rnd]; omega
theorem rnd23_pos (n : Nat) (hn : 0 < n) : 0 < StackNat.rnd (23 * n) := by simp only [StackNat.rnd]; omega

end FvModexp.Amd64.W4En
