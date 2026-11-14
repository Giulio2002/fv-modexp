import FvModexp.Proofs.Amd64.Exp.P2W2Defs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwoWindowSize4` (go-bigmodexpfix nat.go:975-1121), amd64 — code map and entry facts (agent top s48;
amd64 twin of `Arm64.P2W4Defs`, layout as agent divmc's amd64 `P2W2Defs`)

Entry `fn = 0x5e92c0 = 6197952`. Args (Go ABI): `z` AX/BX/CX, `stk` DI, `x` SI/R8/R9, `logM` R10; `y` on the stack
(`[RSP+8..+32)` at entry). Guard `LEAQ -0x278(SP)`, `PUSHQ BP`, `SUBQ $0x2f0` → frame `sp = RSP - 0x2f8`: saved `BP` at
`sp + 0x2f0`, return address at `sp + 0x2f8`, `y` at `sp + 0x300/0x308/0x310`, spills `AX → 0x318`, `CX → 0x328`,
`DI → 0x330`, `SI/R8/R9 → 0x338/0x340/0x348`, `R10 → 0x350`. Open-coded defer of `stk.restore(stk.save())`:
`[0x2c8] = deferwrap1 (0x5e9de0)`, `[0x2d0] = stk`, `[0x2d8] = len₀`, `[0x2e8] = sp + 0x2c8`; flag byte `[0x57] := 1`;
result slots `0x108/0x110/0x118 := 0`.

Code map (offsets from fn; slot map from amd64 P2W2: frame +0x128, defer/arg slots as above, powers headers `0x148 + 24 d`,
d < 16):
* `w = (logM + 63) >> 6` (DX), `nr = rnd(20w) = 20w` (BX), inline `stk.reserve(20w)` (growslice +0x126 ret +0x12b,
  memclr +0x15a ret +0x15f), join `enJ` (+0x1d3), write barrier (+0x1ed, ret +0x1f2), pointer store `enS` (+0x1fc),
  `rsE` (+0x20d, `LEAQ (DX)(DX*1), BX`: DX = w).
* `zz = stk.nat(2w)` (call +0x214, ret +0x219); powers = 16 headers at `0x148..0x2c8`;
  `buildPrecomputationWindowModPower2` (call +0x290, ret +0x295).
* skip loop / `return 1` (makeslice +0x365, newobject +0x38c, `CALL CX` +0x3c8, `RET` +0x3ea).
* first window `z.set(powers[d])` (makeslice +0x4a3 / +0x516, memmove +0x5a2).
* body: 4 × (`sqr` + `trunc`) (+0x681/+0x697, +0x6d7/+0x6ed, +0x72d/+0x743, +0x783/+0x799), `mul` +0x80f, `trunc` +0x825.
* exit `z.set(zz)` (makeslice +0x8f7 / +0x92b, memmove +0x976), closure `CALL AX` +0x9dc, `RET` +0x9fe.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4"
theorem fnBase : segAddr LibW.program fn = 6197952 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 6197952
/-- the join of `slices.Grow` (fn+0x1d3, `MOVQ R12, 8(DI)`) -/
abbrev enJ : Nat := 6198419
/-- return of `growslice` (fn+0x12b) -/
abbrev grRet : Nat := 6198251
/-- return of `memclrNoHeapPointers` (fn+0x15f) -/
abbrev mcRet : Nat := 6198303
/-- return of `gcWriteBarrier2` (fn+0x1f2) -/
abbrev wbRet : Nat := 6198450
/-- the pointer store `MOVQ R11, (DI)` (both write-barrier branches, fn+0x1fc) -/
abbrev enS : Nat := 6198460
/-- after the inline `stk.reserve` (fn+0x20d, `LEAQ (DX)(DX*1), BX`) -/
abbrev rsE : Nat := 6198477
abbrev grE : Nat := P2W2.grE
abbrev mcE : Nat := P2W2.mcE
abbrev wbE : Nat := P2W2.wbE
abbrev wTy : Nat := P2W2.wTy
/-- `nat.expNNPowerOfTwoWindowSize4.deferwrap1` (0x5e9de0) -/
abbrev dwE : Nat := 6200800
theorem dwBase : segAddr LibW.program (fn ++ ".deferwrap1") = dwE := by decide

/-- `w = ⌈logM / 64⌉` (nat.go:981) -/
@[reducible] def W (lm : Nat) : Nat := (lm + 63) / 64

/-- the frame slots after the prologue (saved `BP`, return address, defer record, argument spills, stack argument `y`,
result slots `0x108` and (one 16-byte `MOVUPS X15` store) `0x110..0x120`, defer flag) -/
@[reducible] def ESl (M : Memory) (sp st bp r zp zc xp xl xc yp yl lm len0 : Nat) : Prop :=
  M.readLE (sp + 0x2f0) 8 = bp ∧ M.readLE (sp + 0x2f8) 8 = r ∧ M.readLE (sp + 0x2e8) 8 = sp + 0x2c8 ∧
  M.readLE (sp + 0x2c8) 8 = dwE ∧ M.readLE (sp + 0x2d0) 8 = st ∧ M.readLE (sp + 0x2d8) 8 = len0 ∧
  M.readLE (sp + 0x318) 8 = zp ∧ M.readLE (sp + 0x328) 8 = zc ∧ M.readLE (sp + 0x330) 8 = st ∧
  M.readLE (sp + 0x338) 8 = xp ∧ M.readLE (sp + 0x340) 8 = xl ∧ M.readLE (sp + 0x348) 8 = xc ∧
  M.readLE (sp + 0x300) 8 = yp ∧ M.readLE (sp + 0x308) 8 = yl ∧ M.readLE (sp + 0x350) 8 = lm ∧
  M.readLE (sp + 0x57) 1 = 1 ∧ M.readLE (sp + 0x108) 8 = 0 ∧ M.readLE (sp + 0x110) 16 = 0

/-- the slots `ESl` names lie in `[sp+0x57, sp+0x58) ∪ [sp+0x108, sp+0x120) ∪ [sp+0x2c8, sp+0x2e0) ∪ [sp+0x2e8, sp+0x358)` -/
theorem ESl.keep {M1 M3 : Memory} {sp st bp r zp zc xp xl xc yp yl lm len0 : Nat}
    (h : ESl M1 sp st bp r zp zc xp xl xc yp yl lm len0)
    (hk : ∀ a k, (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58 ∨ sp + 0x108 ≤ a ∧ a + k ≤ sp + 0x120 ∨
      sp + 0x2c8 ≤ a ∧ a + k ≤ sp + 0x2e0 ∨ sp + 0x2e8 ≤ a ∧ a + k ≤ sp + 0x358) → M3.readLE a k = M1.readLE a k) :
    ESl M3 sp st bp r zp zc xp xl xc yp yl lm len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3,
    (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6,
    (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9,
    (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12,
    (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15,
    (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18⟩

/-- the call environment of the entry segment (entry state `s`, `RSP = sp + 0x2f8`, window `[sp - 8 - K, sp + 0x358)`) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (s : State) : Prop :=
  s.regs 4 = BitVec.ofNat 64 (sp + 0x2f8) ∧ s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧
  s.xmm 15 = 0 ∧ s.df = false ∧ sp % 8 = 0 ∧ 41512 ≤ K ∧ K ≤ 2 ^ 20 ∧
  CallW.CEnv R L g fs (sp - 8) K 0x360 s.mem ∧ RunIface.Serves R

/-- `w = (logM + 63) >> 6` (`LEAQ 0x3f(R10), DX; SHRQ $6, DX`, fn+0x79) -/
theorem shr6 (lm : Nat) (h : lm + 63 < 2 ^ 64) : (BitVec.ofNat 64 lm + 63#64) >>> 6 = BitVec.ofNat 64 (W lm) :=
  P2W2.shr6 lm h

theorem rnd20 (w : Nat) : StackNat.rnd (20 * w) = 20 * w := by
  simp only [StackNat.rnd]; omega

end FvModexp.Amd64.P2W4
