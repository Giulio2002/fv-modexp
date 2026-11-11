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

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64

/-! Small arithmetic helpers, proved once in a small context (an `omega` inside a segment proof costs seconds). -/

theorem bv_sub_of_le (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem bv_add_of_lt (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (b + a) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := b + a) (by omega)]
  omega

theorem outA_of {s : State} {a n : Nat} (h : a + n ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ a) :
    Outside a n (winA s stk 40) := by
  simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega

end FvModexp.Arm64.Run
