import FvModexp.Proofs.Amd64.NatQ.KSqrProD
import FvModexp.Proofs.Amd64.NatQ.KSqrLoop
import FvModexp.Proofs.Common.DivmcBits

set_option autoImplicit false

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/KSqrPQ.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the prologue's
shared definitions (`KQ`) and word lemmas, imported by the independent segments KSqrPA / KSqrPB / KSqrPC

`KQ … s M`: the prologue's memory `M` differs from the entry's only in the frame `[RSP - 320, RSP)` and the spill area
`[RSP + 8, RSP + 48)`; it holds the saved `RBP` (at `RSP - 8`) and the spill `RSP + 40 := xp`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

/-- the prologue memory facts (see the module doc) -/
structure KQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State) (M : Memory) :
    Prop where
  pre : KPre R b H L W st zp (2 * n) zc xp n xc s
  fr : MemFrame s.mem M [((s.regs 4).toNat - 320, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 48)]
  reg : M.regions = s.mem.regions
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  s5 : M.readLE ((s.regs 4).toNat + 40) 8 = xp

theorem bv_sub_ofNat {a c : Nat} (h1 : c ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem bv_add_ofNat {a c : Nat} (h : a + c < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 c = BitVec.ofNat 64 (a + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- `NEGQ d; SARQ $63, d; ANDQ y, d` with `0 < d < 2^40` gives `y` (both operand orders) -/
theorem kmask (d y : Nat) (h1 : 0 < d) (h2 : d < 2 ^ 40) :
    ((0#64 - BitVec.ofNat 64 d).sshiftRight 63 &&& BitVec.ofNat 64 y) = BitVec.ofNat 64 y :=
  neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)

theorem kmask' (d y : Nat) (h1 : 0 < d) (h2 : d < 2 ^ 40) :
    (BitVec.ofNat 64 y &&& (0#64 - BitVec.ofNat 64 d).sshiftRight 63) = BitVec.ofNat 64 y := by
  rw [BitVec.and_comm]; exact kmask d y h1 h2

/-- `ANDQ $-2` -/
theorem kand2 (x : BitVec 64) : x &&& 18446744073709551614#64 = (x >>> 1) <<< 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551614#64)[i] = decide (0 < i) := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, c1 i hi]
  by_cases h : i = 0
  · subst h; simp
  · simp [show 1 + (i - 1) = i by omega, show ¬ i < 1 by omega, BitVec.getLsbD_eq_getElem hi] <;>
      (try (intro _; omega))

theorem kshr1 {n : Nat} (h : n + 1 < 2 ^ 64) : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kn2 n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega

theorem kshl3 {a : Nat} (h : a < 2 ^ 40) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem kshl4 {a : Nat} (h : a < 2 ^ 40) : BitVec.ofNat 64 a <<< 4 = BitVec.ofNat 64 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem kshl1 {a : Nat} (h : a < 2 ^ 40) : BitVec.ofNat 64 a <<< 1 = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

end FvModexp.Amd64.Q.NatSqr
