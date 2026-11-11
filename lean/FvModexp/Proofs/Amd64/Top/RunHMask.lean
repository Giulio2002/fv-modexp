import FvModexp.Proofs.Amd64.Top.RunRel
import FvModexp.Proofs.Common.BitArith

/-! # `Run` (amd64): the re-slice mask of `getData` (shared by the header segments) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- The amd64 re-slice mask `(-(cap - start)) >> 63` applied to the start (adapted from agent infra
`Amd64/RequiredGas/Pre.lean`). -/
theorem neg_asr63_and (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    ((0#64 - (a - b)).sshiftRight 63).toNat &&& b.toNat = if b.toNat < a.toNat then b.toNat else 0 := by
  have e : 0#64 - (a - b) = b - a := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e, BitArith.asr63_toNat, BitVec.toNat_sub]
  by_cases h : b.toNat < a.toNat
  · rw [if_neg (by omega), if_pos h, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt b.isLt]
  · rw [if_pos (by omega), if_neg h, Nat.zero_and]

theorem neg_asr63_and' (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    b.toNat &&& ((0#64 - (a - b)).sshiftRight 63).toNat = if b.toNat < a.toNat then b.toNat else 0 := by
  rw [Nat.and_comm]; exact neg_asr63_and a b ha hb

/-- The mask as a `BitVec` equation. -/
theorem neg_asr63_andB (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    ((0#64 - (a - b)).sshiftRight 63 &&& b) = if b.toNat < a.toNat then b else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, neg_asr63_and a b ha hb]
  split <;> simp

theorem neg_asr63_andB' (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    (b &&& (0#64 - (a - b)).sshiftRight 63) = if b.toNat < a.toNat then b else 0#64 := by
  rw [BitVec.and_comm]; exact neg_asr63_andB a b ha hb

end FvModexp.Amd64.Run
