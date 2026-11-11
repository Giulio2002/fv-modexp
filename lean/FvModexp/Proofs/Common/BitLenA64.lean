import FvModexp.Proofs.Common.Util
import FvModexp.Proofs.Common.BitsNat
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.bitLen` (nat.go:346-357) as the arm64 code computes it: smear + `CLZ`, exact value (agent infra)

`smearBV x` is the register chain `ORR R11>>1 … ORR R11>>32`; `CLZ` of it is `CLZ` of `x`, so the computed bit length
`64 - clz + (len-1)<<6` is `64 (len - 1) + bitLen (top limb)` exactly, and a nat with that top limb is `< 2^bitLen`.
-/

open Janus Janus.Arm64 Janus.Spec

namespace FvModexp.BitLenA64

/-- the smear chain as the arm64 code computes it -/
def smearBV (x : BitVec 64) : BitVec 64 :=
  let a := x ||| x >>> 1
  let b := a ||| (x ||| x >>> 1) >>> 2
  let c := b ||| (a ||| (x ||| x >>> 1) >>> 2) >>> 4
  let d := c ||| (b ||| (a ||| (x ||| x >>> 1) >>> 2) >>> 4) >>> 8
  let e := d ||| (c ||| (b ||| (a ||| (x ||| x >>> 1) >>> 2) >>> 4) >>> 8) >>> 16
  e ||| e >>> 32

theorem step (y : BitVec 64) (k : Nat) (h : y.toNat ≠ 0) :
    (y ||| y >>> k).toNat ≠ 0 ∧ Nat.log2 (y ||| y >>> k).toNat = Nat.log2 y.toNat := by
  have e : (y ||| y >>> k).toNat = y.toNat ||| y.toNat >>> k := by
    rw [BitVec.toNat_or, BitVec.toNat_ushiftRight]
  rw [e]; exact ⟨Mdl.or_shr_ne _ _ h, Mdl.or_shr_log2 _ _ h⟩

theorem smearBV_log2 (x : BitVec 64) (h : x.toNat ≠ 0) :
    (smearBV x).toNat ≠ 0 ∧ Nat.log2 (smearBV x).toNat = Nat.log2 x.toNat := by
  unfold smearBV
  obtain ⟨a1, a2⟩ := step x 1 h
  obtain ⟨b1, b2⟩ := step _ 2 a1
  obtain ⟨c1, c2⟩ := step _ 4 b1
  obtain ⟨d1, d2⟩ := step _ 8 c1
  obtain ⟨e1, e2⟩ := step _ 16 d1
  obtain ⟨f1, f2⟩ := step _ 32 e1
  exact ⟨f1, by rw [f2, e2, d2, c2, b2, a2]⟩

theorem smearBV_zero : smearBV 0#64 = 0#64 := by decide

theorem clz_smear (x : BitVec 64) : clzNat 64 (smearBV x).toNat = clzNat 64 x.toNat := by
  have h1 := Util.clz_bl 64 _ (smearBV x).isLt
  have h2 := Util.clz_bl 64 _ x.isLt
  by_cases hx : x.toNat = 0
  · have : x = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx)
    subst this; rw [smearBV_zero]
  · obtain ⟨hs, hl⟩ := smearBV_log2 x hx
    unfold Aux.bitLen at h1 h2
    rw [if_neg hs, hl] at h1; rw [if_neg hx] at h2
    omega

/-- the computed bit length, exact -/
theorem bl_exact (w l : Nat) (hw : w < 2 ^ 64) (h1 : 1 ≤ l) (hl : l ≤ 2 ^ 20) :
    (64#64 - BitVec.ofNat 64 (clzNat 64 w) + (BitVec.ofNat 64 l - 1#64) <<< 6).toNat = 64 * (l - 1) + Aux.bitLen w := by
  have hc := Util.clz_bl 64 w hw
  have hb : Aux.bitLen w ≤ 64 := by omega
  generalize clzNat 64 w = c at *
  have h64 : (64#64 - BitVec.ofNat 64 c).toNat = 64 - c := by
    rw [BitVec.toNat_sub]; simp; omega
  have hs : ((BitVec.ofNat 64 l - 1#64) <<< 6).toNat = 64 * (l - 1) := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub]; simp [Nat.shiftLeft_eq]
    rw [show (18446744073709551615 + l) * 64 = 64 * (l - 1) + 18446744073709551616 * 64 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, h64, hs]
  omega

/-- a nat whose top limb (of `l ≥ 1`) is `w` is below `2 ^ (64 (l-1) + bitLen w)` -/
theorem natVal_lt_bl (m : Memory) (p l : Nat) (h1 : 1 ≤ l) :
    natVal m p l < 2 ^ (64 * (l - 1) + Aux.bitLen (m.readLE (p + 8 * (l - 1)) 8)) := by
  have e := natVal_succ m p (l - 1)
  rw [Nat.sub_add_cancel h1] at e
  rw [e]
  generalize m.readLE (p + 8 * (l - 1)) 8 = w
  have hlo := natVal_lt m p (l - 1)
  have hw : w < 2 ^ Aux.bitLen w := by
    unfold Aux.bitLen; split
    · omega
    · exact Nat.lt_log2_self
  have : 2 ^ (64 * (l - 1)) * w + 2 ^ (64 * (l - 1)) ≤ 2 ^ (64 * (l - 1)) * 2 ^ Aux.bitLen w := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hw
  rw [Nat.pow_add]; omega

end FvModexp.BitLenA64
