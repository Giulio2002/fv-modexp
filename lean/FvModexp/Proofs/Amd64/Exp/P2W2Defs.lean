import FvModexp.Proofs.Amd64.Exp.W2EnDefs
import FvModexp.Proofs.Amd64.Nat.StackNatN
import FvModexp.Proofs.Common.TruncMath

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwoWindowSize2` (go-bigmodexpfix nat.go:1129-1285), amd64 — code map and entry facts (agent divmc s66;
amd64 twin of `Arm64.P2W2Defs`, entry layout as agent expmc's amd64 `W2EnDefs`)

Entry `fn = 0x5e9e20 = 6200864`. Args (Go ABI): `z` AX/BX/CX, `stk` DI, `x` SI/R8/R9, `logM` R10; `y` does not fit the
remaining registers and is passed on the stack (`[RSP+8..+32)` at entry). Guard `LEAQ -0x150(SP)`, `PUSHQ BP`,
`SUBQ $0x1c8` → frame `sp = RSP - 0x1d0`: saved `BP` at `sp + 0x1c8`, return address at `sp + 0x1d0`, `y` at
`sp + 0x1d8/0x1e0/0x1e8`, spills `AX → 0x1f0`, `CX → 0x200`, `DI → 0x208`, `SI/R8/R9 → 0x210/0x218/0x220`,
`R10 → 0x228`. Open-coded defer of `stk.restore(stk.save())`: `[0x1a0] = deferwrap1 (0x5ea880)`, `[0x1a8] = stk`,
`[0x1b0] = len₀`, `[0x1c0] = sp + 0x1a0`; flag byte `[0x57] := 1`; result slots `0x100/0x108/0x110 := 0`.

Code map (offsets from fn):
* `w = (logM + 63) >> 6` (BX; spilled to `0xf8` on the grow path), `nr = rnd(8w) = 8w` (DX, R15; `0xf0`), inline
  `stk.reserve(8w)`: `nr - (cap - len₀) ≤ 0` → join `enJ` (+0x1d3); else `growslice(arr, len₀+nr, cap, len₀+nr-cap, Word)`
  (+0x126, ret +0x12b), `memclrNoHeapPointers` (+0x15a, ret +0x15f), `len₀ ≤ cap'` check → `enJ`. `enJ`: header
  `(len₀, cap)` stores, write barrier (`gcWriteBarrier2` +0x1ee, ret +0x1f3), pointer store `enS` (+0x1fd),
  `len₀ + nr ≤ cap` check, `len := len₀ + nr` → `rsE` (+0x20d, `ADDQ BX, BX`).
* `zz = stk.nat(2w)` (call +0x213, ret +0x218) → `0x118/0x68/0x70`; `powers` = 4 headers at `0x140..0x1a0`, zeroed;
  `buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)` (call +0x284, ret +0x289).
* `mmask` (R10), `mtop = (logM-2) >> 6` (R11), `i = min(len y - 1, mtop)`, `yi = y[i] (& mmask if i == mtop)`; skip loop
  (+0x302 / test +0x30a): `i == 0` → return `1` (+0x32a: `z == nil` → `newobject` `nat{1}` +0x379, else `setWord(1)`
  with `makeslice(1,1)` +0x354 when `cap z = 0`) via `norm` (+0x94f), the deferred closure (`CALL CX` +0x3b5 /
  `CALL AX` +0x992) and `RET`.
* (+0x3d8) `k = (bitLen(yi)+1)/2 - 1`, `d = yi >> 2k < 4`, `z = z.set(powers[d])` (`make`: reuse / `makeslice(1,1)`
  +0x48a / `makeslice(n,n+4)` +0x500; `memmove` +0x58c unless same pointer), `yi <<= 64 - 2k`, `k -= 2` → loop.
* loop test +0x7e0 (`TESTQ R10; JGE`): body +0x645: `zz = trunc(sqr(zz, z))` (+0x672 / +0x688),
  `z' = trunc(sqr(z, zz))` (+0x6c8 / +0x6e0), `trunc(mul(zz, z', powers[yi >> 62]))` (+0x756 / +0x76c), `yi <<= 2`,
  `k--`; outer (+0x7e9): `i == 0` → exit +0x805, else `i--`, `yi = y[i]`, `k = 31`.
* exit: `oddNumberOfSwaps` (`k₀` even, `BTL $0`) → `z.set(zz)` (same `make` / `memmove` shape, +0x837 / +0x86c /
  +0x8b7); `norm` (+0x8db); closure `CALL AX` (+0x91c); `RET` (+0x93e).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2"
theorem fnBase : segAddr LibW.program fn = 6200864 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 6200864
/-- the join of `slices.Grow` (fn+0x1d3, `MOVQ R12, 8(DI)`) -/
abbrev enJ : Nat := 6201331
/-- return of `growslice` (fn+0x12b) -/
abbrev grRet : Nat := 6201163
/-- return of `memclrNoHeapPointers` (fn+0x15f) -/
abbrev mcRet : Nat := 6201215
/-- return of `gcWriteBarrier2` (fn+0x1f3) -/
abbrev wbRet : Nat := 6201363
/-- the pointer store `MOVQ R11, (DI)` (both write-barrier branches, fn+0x1fd) -/
abbrev enS : Nat := 6201373
/-- after the inline `stk.reserve` (fn+0x20d, `ADDQ BX, BX`) -/
abbrev rsE : Nat := 6201389
/-- `runtime.growslice` / `memclrNoHeapPointers` / `gcWriteBarrier2` (contract addresses of the extraction) -/
abbrev grE : Nat := W2En.grE
abbrev mcE : Nat := W2En.mcE
abbrev wbE : Nat := W2En.wbE
/-- the `big.Word` type descriptor -/
abbrev wTy : Nat := W2En.wTy
theorem grE_eq : Extracted.program.contractAddr "runtime.growslice" = grE := W2En.grE_eq
theorem mcE_eq : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = mcE := W2En.mcE_eq
theorem wbE_eq : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbE := W2En.wbE_eq
theorem wTy_eq : StackNat.wT = wTy := rfl

/-- `nat.expNNPowerOfTwoWindowSize2.deferwrap1` (the deferred `stk.restore` closure, 0x5ea880) -/
abbrev dwE : Nat := 6203520

/-- `w = ⌈logM / 64⌉` (nat.go:1135) -/
@[reducible] def W (lm : Nat) : Nat := (lm + 63) / 64

/-- the frame slots after the prologue (saved `BP`, return address, defer record, argument spills, stack argument `y`,
result slots `0x100` and (one 16-byte `MOVUPS X15` store) `0x108..0x118`, defer flag) -/
@[reducible] def ESl (M : Memory) (sp st bp r zp zc xp xl xc yp yl lm len0 : Nat) : Prop :=
  M.readLE (sp + 0x1c8) 8 = bp ∧ M.readLE (sp + 0x1d0) 8 = r ∧ M.readLE (sp + 0x1c0) 8 = sp + 0x1a0 ∧
  M.readLE (sp + 0x1a0) 8 = dwE ∧ M.readLE (sp + 0x1a8) 8 = st ∧ M.readLE (sp + 0x1b0) 8 = len0 ∧
  M.readLE (sp + 0x1f0) 8 = zp ∧ M.readLE (sp + 0x200) 8 = zc ∧ M.readLE (sp + 0x208) 8 = st ∧
  M.readLE (sp + 0x210) 8 = xp ∧ M.readLE (sp + 0x218) 8 = xl ∧ M.readLE (sp + 0x220) 8 = xc ∧
  M.readLE (sp + 0x1d8) 8 = yp ∧ M.readLE (sp + 0x1e0) 8 = yl ∧ M.readLE (sp + 0x228) 8 = lm ∧
  M.readLE (sp + 0x57) 1 = 1 ∧ M.readLE (sp + 0x100) 8 = 0 ∧ M.readLE (sp + 0x108) 16 = 0

/-- the slots `ESl` names lie in `[sp+0x57, sp+0x58) ∪ [sp+0x100, sp+0x118) ∪ [sp+0x1a0, sp+0x1b8) ∪ [sp+0x1c0, sp+0x230)` -/
theorem ESl.keep {M1 M3 : Memory} {sp st bp r zp zc xp xl xc yp yl lm len0 : Nat}
    (h : ESl M1 sp st bp r zp zc xp xl xc yp yl lm len0)
    (hk : ∀ a k, (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58 ∨ sp + 0x100 ≤ a ∧ a + k ≤ sp + 0x118 ∨
      sp + 0x1a0 ≤ a ∧ a + k ≤ sp + 0x1b8 ∨ sp + 0x1c0 ≤ a ∧ a + k ≤ sp + 0x230) → M3.readLE a k = M1.readLE a k) :
    ESl M3 sp st bp r zp zc xp xl xc yp yl lm len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3,
    (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6,
    (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9,
    (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12,
    (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15,
    (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18⟩

/-- the call environment of the entry segment (entry state `s`, `RSP = sp + 0x1d0`, window `[sp - 8 - K, sp + 0x230)`
= the callee stacks, the frame, the saved `BP`, the return address, the stack argument `y` and the register spill area) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (s : State) : Prop :=
  s.regs 4 = BitVec.ofNat 64 (sp + 0x1d0) ∧ s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧
  s.xmm 15 = 0 ∧ s.df = false ∧ sp % 8 = 0 ∧ 41512 ≤ K ∧ K ≤ 2 ^ 20 ∧
  CallW.CEnv R L g fs (sp - 8) K 0x238 s.mem ∧ RunIface.Serves R

/-- `w = (logM + 63) >> 6` (`LEAQ 0x3f(R10), BX; SHRQ $6, BX`, fn+0x79) -/
theorem shr6 (lm : Nat) (h : lm + 63 < 2 ^ 64) : (BitVec.ofNat 64 lm + 63#64) >>> 6 = BitVec.ofNat 64 (W lm) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [W, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show lm < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show lm + 63 % 2 ^ 64 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show (lm + 63) / 64 < 2 ^ 64 by omega)]

theorem rnd8 (w : Nat) : StackNat.rnd (8 * w) = 8 * w := by
  simp only [StackNat.rnd]; omega

/-- `nr = rnd(8w)` (`SHLQ $3, DX; ADDQ $3, DX; ANDQ $-4, DX`, fn+0x84..0x90) -/
theorem nr8 (w : Nat) (hw : w ≤ 2 ^ 12) :
    (BitVec.ofNat 64 w <<< 3 + 3#64) &&& BitVec.ofNat 64 18446744073709551612 = BitVec.ofNat 64 (8 * w) := by
  have e : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]; omega
  rw [e]
  have := StackNat.rnd_bv (BitVec.ofNat 64 (8 * w)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), rnd8] at this
  exact this

end FvModexp.Amd64.P2W2
