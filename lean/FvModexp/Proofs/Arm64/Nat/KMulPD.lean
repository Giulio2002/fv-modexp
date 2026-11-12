import FvModexp.Proofs.Arm64.Nat.KMulB

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the prologue's memory facts (natmul.go:164-206)

`KQm … s M`: the facts of the prologue's memory `M` before the `stk.nat` call: `KPre` at the entry, only our frame
written (`[SP-456, SP-8)`, `[SP+8, SP+72)`), the frame record (`X29`/`X30` at `SP-456`/`SP-448`) and the spills
`SP+16 := zp`, `SP+40 := xp`, `SP+64 := yp`. The prologue segment modules (`KMulPA`, `KMulPB`, `KMulPC`) import this
one only.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (IntAt)

/-- the prologue memory facts (see the module doc) -/
structure KQm (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (M : Memory) : Prop where
  pre : KPre R b L W st zp (2 * n) zc xp n xc yp n yc s
  fr : MemFrame s.mem M [(s.sp.toNat - 456, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]
  reg : M.regions = s.mem.regions
  lr : M.readLE (s.sp.toNat - 448) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 456) 8 = (s.regs 29).toNat
  s2 : M.readLE (s.sp.toNat + 16) 8 = zp
  s5 : M.readLE (s.sp.toNat + 40) 8 = xp
  s6 : M.readLE (s.sp.toNat + 64) 8 = yp

/-- the `n2` facts used by every prologue segment -/
theorem kh_facts {n : Nat} (h : 40 ≤ n) :
    kh n ≤ n ∧ n - kh n ≤ kh n ∧ 0 < kh n ∧ kh n < n ∧ 2 * kh n ≤ n + 1 ∧ n ≤ 2 * kh n := by
  simp only [kh]; omega

/-- `LSR $1` as Janus spells it (copied from this repo's `KSqrPA.klsr1`) -/
theorem km_lsr1 (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (9223372036854775807#64)[i] = decide (i < 63) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 63
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

/-- `LSR $1` of `n + 1` -/
theorem kh_lsr (n : Nat) (h : n < 2 ^ 40) : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kh n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kh]; omega

theorem km_sub {a c : Nat} (h1 : c ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- the `ASR #63` mask of `-(c - n2)` is all ones when `n2 < c < 2^40` -/
theorem km_mask (k c : Nat) (h1 : k < c) (h2 : c < 2 ^ 40) :
    (BitVec.ofNat 64 k &&& (0#64 - BitVec.ofNat 64 (c - k)).sshiftRight 63) = BitVec.ofNat 64 k := by
  rw [BitVec.and_comm]
  exact neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.NatMul
