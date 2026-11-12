import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Nat.StackNatN
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcLsl
import FvModexp.Proofs.Common.TruncMath

/-!
# `nat.expNNPowerOfTwoWindowSize2` (go-bigmodexpfix nat.go:1129-1285), arm64 — code map and entry facts (agent infra)

Entry `0x1b6410 = 1795088`, args `z` X0..X2, `stk` X3, `x` X4..X6, `y` X7..X9, `logM` X10. Frame: guard `SUB $336`
(`morestack` iff `SP - 336 ≤ stackguard`), `SUB $464` → `SP' = SP - 464`, saved FP at `SP' - 8`, LR at `SP'`
(segment lemmas use `sp := SP'`). Argument spills (caller area): `z.ptr` 472, `z.cap` 488, `stk` 496, `x` 504/512/520,
`y.ptr` 528, `y.len` 536, `logM` 552 (`above = 96`). Open-coded defer of `stk.restore(stk.save())`: closure record
`416 = deferwrap1 (0x1b6ba0)`, `424 = stk`, `432 = len₀`; `448 = SP' + 416`; flag byte `95 := 1`; result slots
`256/264/272 := 0`.

Code map (offsets from `SP'`):
* `w = (logM + 63) >> 6` (R11; spilled to 248 on the grow path), inline `stk.reserve(8w)` (`nr = rnd(8w) = 8w`):
  `len₀ + nr ≤ cap` → join `enJ` (0x1b6570); else `growslice(arr, len₀+nr, cap, len₀+nr-cap, Word)` (ret 0x1b64f8),
  `memclrNoHeapPointers` (ret 0x1b6528), `len₀ ≤ cap'` check → `enJ`. `enJ`: header `(len₀, cap)` stores, write
  barrier (`gcWriteBarrier2`, ret 0x1b6588), pointer store (0x1b658c), `len₀ + nr ≤ cap` check, `len := len₀ + nr`
  → `rsE` (0x1b659c).
* `zz = stk.nat(2w)` (call 0x1b65a4, ret 0x1b65a8) → 280/112/120; `powers` = 4 headers at 320..416, zeroed;
  `buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)` (call 0x1b65f0, ret 0x1b65f4).
* `mmask` (R8), `mtop = (logM-2) >> 6`, `i = min(len y - 1, mtop)`, `yi = y[i] (& mmask if i == mtop)`; skip loop
  (head 0x1b665c: `CBNZ yi`): `i == 0` → return `1` (0x1b6674: `z == nil` → `newobject` `nat{1}`, else `setWord(1)`
  with `makeslice(1,1)` when `cap z = 0`) via `norm`, the deferred closure (`CALL (R1)` / `CALL (R0)`) and `RET`.
* (0x1b66f4) `k = (bitLen(yi)+1)/2 - 1`, `d = yi >> 2k < 4`, `z = z.set(powers[d])` (`make`: reuse / `makeslice(1,1)` /
  `makeslice(n,n+4)`; `memmove` unless same pointer), `yi <<= 64 - 2k` (0 if `k = 0`), `k -= 1` → loop test.
* loop test 0x1b69bc (`TBZ $63, k`): body 0x1b6898: `zz = trunc(sqr(zz, z))` (calls 0x1b68bc / 0x1b68d0),
  `z' = trunc(sqr(z, zz))` (0x1b68fc / 0x1b6910), `trunc(mul(zz, z', powers[yi >> 62]))` (0x1b6968 / 0x1b697c),
  `yi <<= 2`, `k--`; outer: `i == 0` → exit 0x1b69dc, else `i--`, `yi = y[i]`, `k = 31`.
* exit: `oddNumberOfSwaps` (`k₀` even) → `z.set(zz)` (same `make` / `memmove` shape); `norm`; closure; `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2"
theorem fnBase : segAddr LibW.program fn = 1795088 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 1795088
/-- the join of `slices.Grow` (fn+0x160, `STP (R14, R12), 8(R3)`) -/
abbrev enJ : Nat := 1795440
/-- return of `growslice` (fn+0xe8) -/
abbrev grRet : Nat := 1795320
/-- return of `memclrNoHeapPointers` (fn+0x118) -/
abbrev mcRet : Nat := 1795368
/-- return of `gcWriteBarrier2` (fn+0x178) -/
abbrev wbRet : Nat := 1795464
/-- the pointer store `MOVD R13, (R3)` (fn+0x17c) -/
abbrev enS : Nat := 1795468
/-- after the inline `stk.reserve` (fn+0x18c, `ADD R11, R11, R1`) -/
abbrev rsE : Nat := 1795484
/-- `runtime.growslice` / `memclrNoHeapPointers` / `gcWriteBarrier2` (contract addresses of the extraction) -/
abbrev grE : Nat := 587552
abbrev mcE : Nat := 608976
abbrev wbE : Nat := 608160
/-- the `big.Word` type descriptor -/
abbrev wTy : Nat := 2641088
/-- `nat.expNNPowerOfTwoWindowSize2.deferwrap1` (the deferred `stk.restore` closure) -/
abbrev dwE : Nat := 1797024

theorem grE_eq : Extracted.program.contractAddr "runtime.growslice" = grE := by decide
theorem mcE_eq : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = mcE := by decide
theorem wbE_eq : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbE := by decide

/-- `w = ⌈logM / 64⌉` (nat.go:1135) -/
@[reducible] def W (lm : Nat) : Nat := (lm + 63) / 64

/-- the frame slots after the prologue (saved FP/LR, defer record, argument spills, result slots, defer flag) -/
@[reducible] def ESl (M : Memory) (sp st : Nat) (r29 : BitVec 64) (ret zp zc xp xl xc yp yl lm len0 : Nat) : Prop :=
  M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ M.readLE (sp + 448) 8 = sp + 416 ∧
  M.readLE (sp + 416) 8 = dwE ∧ M.readLE (sp + 424) 8 = st ∧ M.readLE (sp + 432) 8 = len0 ∧
  M.readLE (sp + 472) 8 = zp ∧ M.readLE (sp + 488) 8 = zc ∧ M.readLE (sp + 496) 8 = st ∧
  M.readLE (sp + 504) 8 = xp ∧ M.readLE (sp + 512) 8 = xl ∧ M.readLE (sp + 520) 8 = xc ∧
  M.readLE (sp + 528) 8 = yp ∧ M.readLE (sp + 536) 8 = yl ∧ M.readLE (sp + 552) 8 = lm ∧
  M.readLE (sp + 95) 1 = 1 ∧ M.readLE (sp + 256) 8 = 0 ∧ M.readLE (sp + 264) 8 = 0 ∧ M.readLE (sp + 272) 8 = 0

theorem ESl.keep {M1 M3 : Memory} {sp st : Nat} {r29 : BitVec 64} {ret zp zc xp xl xc yp yl lm len0 : Nat}
    (h : ESl M1 sp st r29 ret zp zc xp xl xc yp yl lm len0)
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 95 ≤ a ∧ a + k ≤ sp + 96 ∨ sp + 256 ≤ a ∧ a + k ≤ sp + 280 ∨
      sp + 416 ≤ a ∧ a + k ≤ sp + 456 ∨ sp + 472 ≤ a ∧ a + k ≤ sp + 560) → M3.readLE a k = M1.readLE a k)
    (hsp : 8 ≤ sp) : ESl M3 sp st r29 ret zp zc xp xl xc yp yl lm len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3, (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6, (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9, (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12, (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15, (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18, (hk _ _ (by omega)).trans a19⟩

theorem shr6 (lm : Nat) (h : lm + 63 < 2 ^ 64) : BitVec.ofNat 64 (lm + 63) >>> 6 = BitVec.ofNat 64 (W lm) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by simp only [W]; omega)]

theorem rnd8 (w : Nat) : StackNat.rnd (8 * w) = 8 * w := by
  simp only [StackNat.rnd]; omega


/-- `LSL $2` as the executor states it (rotate + masks) (copied from agent expmc's `W2Loop.lsl2`) -/
theorem lsl2 (x : BitVec 64) :
    x.rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64 = x <<< 2 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551612#64)[i] = decide (2 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 2
  · simp [h]
  · simp [h]; omega

/-- `nr = rnd(8w)` as computed at fn+0x54..0x6c: `((w + w) << 2 + 3) &^ 3` -/
theorem nr8 (w : Nat) (hw : w ≤ 2 ^ 12) :
    ((BitVec.ofNat 64 w + BitVec.ofNat 64 w).rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64)
      + 3#64 &&& BitVec.ofNat 64 18446744073709551612 = BitVec.ofNat 64 (8 * w) := by
  have e : (BitVec.ofNat 64 w + BitVec.ofNat 64 w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]; omega
  rw [lsl2, e]
  have := StackNat.rnd_bv (BitVec.ofNat 64 (8 * w)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), rnd8]

end FvModexp.Arm64.P2W2
