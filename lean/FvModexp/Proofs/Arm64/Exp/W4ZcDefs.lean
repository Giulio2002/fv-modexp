import FvModexp.Proofs.Arm64.Exp.W4PowAll
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

/-!
# window-4 prologue (arm64), first-window helpers: definitions and pure lemmas for `W4ZcC`/`W4ZcB`/`W4Zc`

From `zj` (fn+0x774, the join after `z = z.make(2n)`: X0 = z, X14 = cap z) to the loop test (fn+0xaa0).
`zz` (the `lsh` result, cap ≥ 2n+1) is reused; `bitLen(y[len-1])` by smear + `CLZ` (Common/BitLenA64);
`k = (bitLen+3)/4 - 1`, `copy(z, powers[yi >> 4k])` (memmove), `yi <<= 64 - 4k`, `k--`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the join after `z = z.make(2n)` (`CMP R14, R13`, fn+0x774) -/
abbrev zj : Nat := 1800420
/-- the loop test literal (`W4Loop.test`) -/
abbrev testL : Nat := 1801232

/-- the frame words `zj → test` writes besides `z[0:n]` and `R.rt` (memmove's window, spills) -/
@[reducible] def cw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 144, sp + 152), (sp + 184, sp + 192), (sp + 232, sp + 240), (sp + 240, sp + 248),
    (sp + 296, sp + 304), (sp + 328, sp + 336), (sp + 368, sp + 376), (sp + 872, sp + 880)]

/-- the index of the most significant non-zero window of the top word (`k`, nat.go:1438) -/
abbrev kTop (yi : Nat) : Nat := (Exp.bitLen yi + 3) / 4 - 1

theorem lsr2 (x : BitVec 64) :
    x.rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64 = x >>> 2 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (4611686018427387903#64)[i] = decide (i < 62) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 62
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

theorem lsl2 (x : BitVec 64) :
    x.rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64 = x <<< 2 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551612#64)[i] = decide (2 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 2
  · simp [h]
  · simp [h]; omega

theorem lsl3 (x : BitVec 64) :
    x.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64 = x <<< 3 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551608#64)[i] = decide (3 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 3
  · simp [h]
  · simp [h]; omega

theorem e8n (n : Nat) (hn : n ≤ 2 ^ 16) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem bitLen_pos (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : 1 ≤ Exp.bitLen yi ∧ Exp.bitLen yi ≤ 64 := by
  unfold Exp.bitLen
  rw [if_neg (by omega)]
  have := Nat.log2_lt (show yi ≠ 0 by omega) |>.2 h
  omega

theorem e21 (bl : BitVec 64) (yi : Nat) (hb : bl.toNat = Exp.bitLen yi) (h0 : 0 < yi) (h : yi < 2 ^ 64) :
    (bl + 3#64) >>> 2 = BitVec.ofNat 64 (kTop yi + 1) := by
  have := bitLen_pos yi h0 h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, hb, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kTop,
    Nat.reducePow]
  omega

theorem kTop_le (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : kTop yi ≤ 15 ∧ yi / 2 ^ (kTop yi * 4) < 16 := by
  have hb := bitLen_pos yi h0 h
  refine ⟨by unfold kTop; omega, ?_⟩
  have h1 : yi < 2 ^ Exp.bitLen yi := by
    unfold Exp.bitLen; rw [if_neg (by omega)]; exact Nat.lt_log2_self
  have h2 : 2 ^ Exp.bitLen yi ≤ 2 ^ (kTop yi * 4) * 16 := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by unfold kTop; omega)
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm]; omega)

theorem e23 (k : Nat) (hk : k ≤ 15) : BitVec.ofNat 64 k <<< 2 = BitVec.ofNat 64 (k * 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem ed (yi k : Nat) (h : yi < 2 ^ 64) :
    BitVec.ofNat 64 yi >>> (k * 4) = BitVec.ofNat 64 (yi / 2 ^ (k * 4)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem lf_chain {M Mw m1 : Memory} {L W zs : List (Nat × Nat)} (hw : MemFrame M Mw W)
    (hws : ∀ a k, InRanges a k L → Outside a k W) (h1 : LiveFrame Mw m1 L zs) : LiveFrame M m1 L zs :=
  (FvModexp.Expmc.liveFrame_of_frame (ws := zs) hw (fun a k hin _ => hws a k hin)).trans h1 (fun _ _ h => h)

theorem mf_chain {M Mw m1 : Memory} {W W1 W2 : List (Nat × Nat)} (hw : MemFrame M Mw W) (h1 : MemFrame Mw m1 W1)
    (hs : ∀ a k, Outside a k W2 → Outside a k W ∧ Outside a k W1) : MemFrame M m1 W2 := hw.trans h1 hs

theorem e20 (yi k : Nat) (hk : k ≤ 15) :
    (if 64 - k * 4 < 64 then BitVec.ofNat 64 (yi * 2 ^ ((64 - k * 4) % 64)) else 0#64) =
      BitVec.ofNat 64 (yi * 2 ^ (64 - k * 4) % 2 ^ 64) := by
  by_cases h0 : k = 0
  · subst h0; simp
  · rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
    apply BitVec.eq_of_toNat_eq; simp

theorem e21' (k : Nat) (hk : k ≤ 15) : BitVec.ofNat 64 (k + 1) - 2#64 = BitVec.ofNat 64 k - 1#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

end FvModexp.Arm64.W4Pro
