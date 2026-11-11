import FvModexp.Proofs.Arm64.Top.RunDRel

/-! # `Run` (arm64): the slice-pointer mask of `input[start:]` as a natural number -/

open Janus Janus.Arm64

namespace FvModexp.Arm64.Run

/-- Go's slice-pointer mask `start & ((start - cap) >> 63)` for `start ≤ cap < 2^63`: `start` when `start < cap`, else 0. -/
theorem sliceMask_le (e c : Nat) (h : e ≤ c) (hc : c < 2 ^ 63) :
    (BitVec.ofNat 64 e &&& (BitVec.ofNat 64 e - BitVec.ofNat 64 c).sshiftRight 63).toNat = if e < c then e else 0 := by
  split
  · rename_i hlt
    rw [BitVec.toNat_and]
    have := sliceMask_lt e (BitVec.ofNat 64 e) (BitVec.ofNat 64 c)
      (by simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (by simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega) (by omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact this
  · obtain rfl : e = c := by omega
    simp

end FvModexp.Arm64.Run
