import FvModexp.Proofs.Arm64.Nat.KSqrProD
import FvModexp.Proofs.Arm64.Nat.KSqrLoop

set_option autoImplicit false

/-!
# `karatsubaSqr` (arm64): the prologue's shared definitions (`KQ`) and bit lemmas, imported by the independent
segments KSqrPA / KSqrPB / KSqrPC (split out of KSqrPA, 176 s, ROW-TIME LESSON)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- `LSR $1` as Janus spells it (copied from agent expmc's `Exp/W2ZcDefs.lsr1`) -/
theorem klsr1 (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (9223372036854775807#64)[i] = decide (i < 63) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 63
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

/-- the prologue memory facts (see the module doc) -/
structure KQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State) (M : Memory) :
    Prop where
  pre : KPre R b L W st zp (2 * n) zc xp n xc s
  fr : MemFrame s.mem M [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)]
  reg : M.regions = s.mem.regions
  lr : M.readLE (s.sp.toNat - 320) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 328) 8 = (s.regs 29).toNat
  s5 : M.readLE (s.sp.toNat + 40) 8 = xp

theorem bv_sub_ofNat {a c : Nat} (h1 : c ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- `kn2 n ≤ c` (`c < 2^40`) makes the `ASR #63` mask of `-(c - kn2 n)` all ones -/
theorem kmask (n c : Nat) (h1 : kn2 n < c) (h2 : c < 2 ^ 40) :
    (BitVec.ofNat 64 (kn2 n) &&& (0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 (kn2 n))).sshiftRight 63) =
      BitVec.ofNat 64 (kn2 n) := by
  rw [BitVec.and_comm]
  have hd : (BitVec.ofNat 64 c - BitVec.ofNat 64 (kn2 n)).toNat = c - kn2 n := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  exact neg_sshr63_and _ _ (by rw [hd]; omega) (by rw [hd]; omega)

/-- `AND $-2` -/
theorem kand2 (x : BitVec 64) : x &&& 18446744073709551614#64 = (x >>> 1) <<< 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551614#64)[i] = decide (0 < i) := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, c1 i hi]
  by_cases h : i = 0
  · subst h; simp
  · simp [show 1 + (i - 1) = i by omega, show ¬ i < 1 by omega, BitVec.getLsbD_eq_getElem hi] <;>
      (try (intro _; omega))

end FvModexp.Arm64.NatSqr
