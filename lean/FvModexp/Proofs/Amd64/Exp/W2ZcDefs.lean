import FvModexp.Proofs.Amd64.Exp.W2Defs
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.ExpBase
import FvModexp.Proofs.Common.GenReg
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# window-2 prologue (amd64), first window: definitions and pure lemmas (agent expmc s48)

Twin of `Arm64.W2ZcDefs`. From `zj` = fn+0xbcf (the join after `z = z.make(2n)[:n]`, `zz = zz.make(2n)[:n]`:
AX = z, DX = cap z, CX = zz, R12 = cap zz, R11 = n) to the loop test fn+0xf76: `bitLen(y[len-1])` by smear +
`BSRQ` (+0xc29), `k = (bitLen+1)/2 - 1`, `d = yi >> 2k`, the table header loads, `min(n, len powers[d])`, the
`z == powers[d]` test (refuted), `copy(z, powers[d])` (memmove, +0xcc9), `yi <<= 64 - 2k`, `k--`, `i = len y - 1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

/-- the join after `zz = zz.make(2n)[:n]` (fn+0xbcf) -/
abbrev zj : Nat := 6213583
/-- the loop test literal (`W2Loop.test`) -/
abbrev testL : Nat := 6214518

/-- a power-table entry `powers[d]` at memory `M` (header at `sp + 0x1b0 + 24 d`) -/
@[reducible] def Ent (sp n : Nat) (pp pcap tbl : Nat → Nat) (M : Memory) (d : Nat) : Prop :=
  M.readLE (pp d) (8 * n) = tbl d ∧ M.readLE (sp + 0x1b0 + 24 * d) 8 = pp d ∧
  M.readLE (sp + 0x1b8 + 24 * d) 8 = n ∧ M.readLE (sp + 0x1c0 + 24 * d) 8 = pcap d

/-- the frame words `zj → test` writes besides `z[0:n]` and `R.rt` (memmove's window, spills) -/
@[reducible] def cw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4296, sp + 0x18), (sp + 0xe8, sp + 0xf0), (sp + 0x118, sp + 0x128), (sp + 0x140, sp + 0x150),
    (sp + 0x258, sp + 0x260)]

/-- the index of the most significant non-zero window of the top word (`k`, nat.go:1571) -/
abbrev kTop (yi : Nat) : Nat := (Exp.bitLen yi + 1) / 2 - 1

theorem bitLen_pos (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : 1 ≤ Exp.bitLen yi ∧ Exp.bitLen yi ≤ 64 := by
  unfold Exp.bitLen
  rw [if_neg (by omega)]
  have := Nat.log2_lt (show yi ≠ 0 by omega) |>.2 h
  omega

theorem kTop_le (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : kTop yi ≤ 31 ∧ yi / 2 ^ (kTop yi * 2) < 4 := by
  have hb := bitLen_pos yi h0 h
  refine ⟨by unfold kTop; omega, ?_⟩
  have h1 : yi < 2 ^ Exp.bitLen yi := by
    unfold Exp.bitLen; rw [if_neg (by omega)]; exact Nat.lt_log2_self
  have h2 : 2 ^ Exp.bitLen yi ≤ 2 ^ (kTop yi * 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by unfold kTop; omega)
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm]; omega)

theorem ek1 (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) :
    (BitVec.ofNat 64 (Exp.bitLen yi - 1) + 2#64) >>> 1 = BitVec.ofNat 64 (kTop yi + 1) := by
  have := bitLen_pos yi h0 h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kTop,
    Nat.reducePow]
  omega

theorem ek2 (k : Nat) (hk : k ≤ 31) : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem ek3 (k : Nat) (hk : k ≤ 31) : BitVec.ofNat 64 k <<< 1 = BitVec.ofNat 64 (k * 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem ed (yi k : Nat) (h : yi < 2 ^ 64) :
    BitVec.ofNat 64 yi >>> (k * 2) = BitVec.ofNat 64 (yi / 2 ^ (k * 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem and1 (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  have : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  rw [this, BitVec.and_allOnes]

theorem lf_chain {M Mw m1 : Memory} {L W zs : List (Nat × Nat)} (hw : MemFrame M Mw W)
    (hws : ∀ a k, InRanges a k L → Outside a k W) (h1 : LiveFrame Mw m1 L zs) : LiveFrame M m1 L zs :=
  (FvModexp.Expmc.liveFrame_of_frame (ws := zs) hw (fun a k hin _ => hws a k hin)).trans h1 (fun _ _ h => h)

theorem mf_chain {M Mw m1 : Memory} {W W1 W2 : List (Nat × Nat)} (hw : MemFrame M Mw W) (h1 : MemFrame Mw m1 W1)
    (hs : ∀ a k, Outside a k W2 → Outside a k W ∧ Outside a k W1) : MemFrame M m1 W2 := hw.trans h1 hs

theorem en (k : Nat) (hk : k ≤ 31) : 0#64 - (BitVec.ofNat 64 (k * 2) - 64#64) = BitVec.ofNat 64 (64 - k * 2) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem eyk (yi k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 31) :
    (BitVec.ofNat 64 yi <<< ((18446744073709551616 - k * 2) % 64) &&&
      if 64 - k * 2 < 64 then 18446744073709551615#64 else 0#64) = BitVec.ofNat 64 (yi * 2 ^ (64 - k * 2) % 2 ^ 64) := by
  rw [if_pos (by omega), and1, show (18446744073709551616 - k * 2) % 64 = 64 - k * 2 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mod_mod]

theorem ey0 (yi : Nat) : (BitVec.ofNat 64 yi &&& 0#64) = BitVec.ofNat 64 (yi * 2 ^ (64 - 0 * 2) % 2 ^ 64) := by
  rw [BitVec.and_zero]; apply BitVec.eq_of_toNat_eq; simp

theorem ek21 (k : Nat) (hk : k ≤ 31) : BitVec.ofNat 64 (k + 1) - 2#64 = BitVec.ofNat 64 k - 1#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem eyl (ylen : Nat) (h0 : 0 < ylen) (h : ylen < 2 ^ 40) : BitVec.ofNat 64 ylen - 1#64 = BitVec.ofNat 64 (ylen - 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- the smear chain as the amd64 code computes it (`SHRQ k; ORQ`: shifted value on the left) -/
def smearR (x : BitVec 64) : BitVec 64 :=
  let a := x >>> 1 ||| x
  let b := a >>> 2 ||| a
  let c := b >>> 4 ||| b
  let d := c >>> 8 ||| c
  let e := d >>> 16 ||| d
  e >>> 32 ||| e

theorem or_c (a b : BitVec 64) : (a ||| b) = (b ||| a) := BitVec.or_comm a b

theorem smearR_eq (x : BitVec 64) : smearR x = BitLenA64.smearBV x := by
  unfold smearR BitLenA64.smearBV
  simp only [or_c (x >>> 1) x, or_c ((x ||| x >>> 1) >>> 2)]
  generalize ha : (x ||| x >>> 1 ||| (x ||| x >>> 1) >>> 2) = a
  simp only [or_c (a >>> 4) a]
  generalize hb : (a ||| a >>> 4) = b
  simp only [or_c (b >>> 8) b]
  generalize hc : (b ||| b >>> 8) = c
  simp only [or_c (c >>> 16) c]
  generalize hd : (c ||| c >>> 16) = d
  simp only [or_c (d >>> 32) d]

end FvModexp.Amd64.W2Pro
