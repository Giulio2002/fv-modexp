import FvModexp.Proofs.Arm64.Exp.P2W2Defs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwoWindowSize4` (go-bigmodexpfix nat.go:975-1127), arm64 — code map and entry facts (agent infra)

Same layout as the window-2 function (`P2W2Defs`); differences: window 4 (16 powers), frame 752, `stk.reserve(20w)`.

Entry `0x1b5ba0 = 1792928`, args `z` X0..X2, `stk` X3, `x` X4..X6, `y` X7..X9, `logM` X10. Frame: guard `SUB $624`
(`morestack` iff `SP - 624 ≤ stackguard`), `SUB $752` → `SP' = SP - 752`, saved FP at `SP' - 8`, LR at `SP'`
(segment lemmas use `sp := SP'`). Argument spills (caller area): `z.ptr` 760, `z.cap` 776, `stk` 784, `x` 792/800/808,
`y.ptr` 816, `y.len` 824, `logM` 840 (`above = 96`). Open-coded defer of `stk.restore(stk.save())`: closure record
`704 = deferwrap1 (0x1b63c0)`, `712 = stk`, `720 = len₀`; `736 = SP' + 704`; flag byte `95 := 1`; result slots
`256/264/272 := 0`.

Code map (offsets from `SP'`):
* `w = (logM + 63) >> 6` (R9; spilled to 248 on the grow path), inline `stk.reserve(20w)` (`nr = rnd(20w) = 20w`, R11):
  `len₀ + nr ≤ cap` → join `enJ` (0x1b5d04); else `growslice(arr, len₀+nr, cap, len₀+nr-cap, Word)` (ret 0x1b5c8c),
  `memclrNoHeapPointers` (ret 0x1b5cbc), `len₀ ≤ cap'` check, reloads → `enJ`. `enJ`: header `(len₀, cap)` stores, write
  barrier (`gcWriteBarrier2`, ret 0x1b5d1c), pointer store (0x1b5d20), `len₀ + nr ≤ cap` check, `len := len₀ + nr`
  → `rsE` (0x1b5d30).
* `zz = stk.nat(2w)` (call 0x1b5d38, ret 0x1b5d3c) → 280/112/120; `powers` = 16 headers at 320..704, zeroed by a
  6-round `STP.P` loop (0x1b5d50..0x1b5d64); `buildPrecomputationWindowModPower2(stk, powers[:], 4, logM, x)`
  (call 0x1b5d8c, ret 0x1b5d90).
* `mmask` (R8), `mtop = (logM-2) >> 6`, `i = min(len y - 1, mtop)`, `yi = y[i] (& mmask if i == mtop)`; skip loop
  (`CBNZ yi` at 0x1b5df8): `i == 0` → return `1` (0x1b5e10: `z == nil` → `newobject` `nat{1}`, else `setWord(1)`
  with `makeslice(1,1)` when `cap z = 0`) via `norm`, the deferred closure (`CALL (R1)` / `CALL (R0)`) and `RET`.
* (0x1b5e90) `k = (bitLen(yi)+3)/4 - 1`, `d = yi >> 4k < 16`, `z = z.set(powers[d])` (`make`: reuse / `makeslice(1,1)` /
  `makeslice(n,n+4)`; `memmove` unless same pointer), `yi <<= 64 - 4k` (0 if `k = 0`), `k -= 1` → loop test.
* loop test 0x1b61e0 (`TBZ $63, k`): body 0x1b6034: 4 × (`sqr`, `trunc`) with spills `728/232/120` (zz) and
  `280/112/216` (z) (calls 0x1b6058/0x1b606c, 0x1b6098/0x1b60ac, 0x1b60d8/0x1b60ec, 0x1b6118/0x1b612c), then
  `trunc(mul(zz, z, powers[yi >> 60]))` (0x1b6184 / 0x1b6198), `yi <<= 4`, `k--`; outer: `i == 0` → exit 0x1b61f8, else
  `i--`, `yi = y[i]`, `k = 15`.
* exit: `oddNumberOfSwaps` (`k₀` even) → `z.set(zz)` (same `make` / `memmove` shape); `norm`; closure; `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4"
theorem fnBase : segAddr LibW.program fn = 1792928 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 1792928
/-- the join of `slices.Grow` (fn+0x164, `STP (R14, R12), 8(R3)`) -/
abbrev enJ : Nat := 1793284
/-- return of `growslice` (fn+0xec) -/
abbrev grRet : Nat := 1793164
/-- return of `memclrNoHeapPointers` (fn+0x11c) -/
abbrev mcRet : Nat := 1793212
/-- return of `gcWriteBarrier2` (fn+0x17c) -/
abbrev wbRet : Nat := 1793308
/-- the pointer store `MOVD R13, (R3)` (fn+0x180) -/
abbrev enS : Nat := 1793312
/-- after the inline `stk.reserve` (fn+0x190, `ADD R9, R9, R1`) -/
abbrev rsE : Nat := 1793328
/-- `nat.expNNPowerOfTwoWindowSize4.deferwrap1` (the deferred `stk.restore` closure) -/
abbrev dwE : Nat := 1795008

/-- `w = ⌈logM / 64⌉` (nat.go:981) -/
@[reducible] def W (lm : Nat) : Nat := (lm + 63) / 64

/-- the frame slots after the prologue (saved FP/LR, defer record, argument spills, result slots, defer flag) -/
@[reducible] def ESl (M : Memory) (sp st : Nat) (r29 : BitVec 64) (ret zp zc xp xl xc yp yl lm len0 : Nat) : Prop :=
  M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ M.readLE (sp + 736) 8 = sp + 704 ∧
  M.readLE (sp + 704) 8 = dwE ∧ M.readLE (sp + 712) 8 = st ∧ M.readLE (sp + 720) 8 = len0 ∧
  M.readLE (sp + 760) 8 = zp ∧ M.readLE (sp + 776) 8 = zc ∧ M.readLE (sp + 784) 8 = st ∧
  M.readLE (sp + 792) 8 = xp ∧ M.readLE (sp + 800) 8 = xl ∧ M.readLE (sp + 808) 8 = xc ∧
  M.readLE (sp + 816) 8 = yp ∧ M.readLE (sp + 824) 8 = yl ∧ M.readLE (sp + 840) 8 = lm ∧
  M.readLE (sp + 95) 1 = 1 ∧ M.readLE (sp + 256) 8 = 0 ∧ M.readLE (sp + 264) 8 = 0 ∧ M.readLE (sp + 272) 8 = 0

theorem ESl.keep {M1 M3 : Memory} {sp st : Nat} {r29 : BitVec 64} {ret zp zc xp xl xc yp yl lm len0 : Nat}
    (h : ESl M1 sp st r29 ret zp zc xp xl xc yp yl lm len0)
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 95 ≤ a ∧ a + k ≤ sp + 96 ∨ sp + 256 ≤ a ∧ a + k ≤ sp + 280 ∨
      sp + 704 ≤ a ∧ a + k ≤ sp + 744 ∨ sp + 760 ≤ a ∧ a + k ≤ sp + 848) → M3.readLE a k = M1.readLE a k)
    (hsp : 8 ≤ sp) : ESl M3 sp st r29 ret zp zc xp xl xc yp yl lm len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3, (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6, (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9, (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12, (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15, (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18, (hk _ _ (by omega)).trans a19⟩

theorem rnd20 (w : Nat) : StackNat.rnd (20 * w) = 20 * w := by
  simp only [StackNat.rnd]; omega

/-- `nr = rnd(20w)` as computed at fn+0x5c..0x6c: `(w << 2 + (w << 2) << 2 + 3) &^ 3` -/
theorem nr20 (w : Nat) (hw : w ≤ 128) :
    ((BitVec.ofNat 64 w).rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64) +
        ((BitVec.ofNat 64 w).rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64) <<< 2
      + 3#64 &&& 18446744073709551612#64 = BitVec.ofNat 64 (20 * w) := by
  have e : BitVec.ofNat 64 w <<< 2 + (BitVec.ofNat 64 w <<< 2) <<< 2 = BitVec.ofNat 64 (20 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]; omega
  rw [P2W2.lsl2, e]
  have := StackNat.rnd_bv (BitVec.ofNat 64 (20 * w)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), rnd20]

end FvModexp.Arm64.P2W4
