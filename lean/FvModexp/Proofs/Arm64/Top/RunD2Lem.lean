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

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.Tactic

/-- A `memmove` into a stack buffer of the window: its frame (runtime ranges, callee stack, the buffer) is inside
`R.rt ∪ winA`. -/
theorem out_csw {rt : List (Nat × Nat)} {sp a n d k : Nat} (hsp : 4800 ≤ sp) (hd1 : sp - 4800 ≤ d) (hd2 : d + k ≤ sp - 8)
    (h : Outside a n (rt ++ [(sp - 4800, sp - 8), (sp + 8, sp + 40)])) :
    Outside a n (rt ++ [(sp - 624 - 4096, sp - 624 - 8), (sp - 624 + 8, sp - 624 + 8 + 24)] ++ [(d, d + k)]) := by
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  exact ⟨⟨h.1, by omega, by omega⟩, by omega⟩

end FvModexp.Arm64.Run
