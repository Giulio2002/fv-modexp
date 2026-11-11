import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Common.BitsNat

/-!
# `(*stack).nat` (nat.go:319-329, go-bigmodexpfix): budget and rounding facts (ISA independent)

`s.w = slices.Grow(s.w, nr)` (slices.go:421-428) calls `growslice(w, len + nr, cap, len + nr - cap, Word)` when
`cap < len + nr` (`nr = (n + 3) &^ 3`). Its block (`8 · growCap8 (len + nr) cap`, Janus `Alloc.lean`) is bounded by
`stackNatCost len n` (agent expmc's `ExpHyp.stackNatCost`, top's `B_nat`): `nextslicecap N c ≤ 2 N` for `c < N`.
-/

namespace FvModexp

open Janus.Contracts

/-- top's `B_nat n` budget bound (a grow allocates at most `2·(len + round4 n) + 4` words) — expmc's `ExpHyp.stackNatCost` -/
def stackNatCost (len n : Nat) : Nat := allocCost (8 * (2 * (len + n + 3) + 4))

private theorem go_le2 (N : Nat) (hN : 256 ≤ N) : ∀ c, c < N → nextslicecap.go N c ≤ 2 * N := by
  intro c
  induction c using nextslicecap.go.induct N with
  | case1 c c' hc' => intro h; unfold nextslicecap.go; simp only [c'] at *; split <;> omega
  | case2 c c' hc' ih => intro h; unfold nextslicecap.go; simp only [c'] at *; split
                         · omega
                         · exact ih (by omega)

/-- `nextslicecap` grows a shorter slice to at most `2·newLen`. -/
theorem nextslicecap_le2 (N c : Nat) (h : c < N) : nextslicecap N c ≤ 2 * N := by
  unfold nextslicecap
  split
  · omega
  · split
    · omega
    · exact go_le2 N (by omega) c h

/-- `growslice`'s block for `(*stack).nat` fits `stackNatCost`. -/
theorem growRound_le_cost (len n c : Nat) (hc : c < len + (n + 3) / 4 * 4) :
    8 * growCap8 (len + (n + 3) / 4 * 4) c ≤ stackNatCost len n := by
  unfold growCap8 stackNatCost allocCost
  have h1 := roundupsize_le (nextslicecap (len + (n + 3) / 4 * 4) c * 8) true
  have h2 := nextslicecap_le2 _ _ hc
  omega

/-- the new capacity is small -/
theorem growCap_lt (len n c : Nat) (hc : c < len + (n + 3) / 4 * 4) (h : len + n + 3 ≤ 2 ^ 16) :
    growCap8 (len + (n + 3) / 4 * 4) c < 2 ^ 40 := by
  have := growRound_le_cost len n c hc
  unfold stackNatCost allocCost at this
  omega

theorem stackRound_toNat (n : BitVec 64) (h : n.toNat + 3 < 2 ^ 64) :
    ((n + 3#64) &&& BitVec.ofNat 64 18446744073709551612).toNat = (n.toNat + 3) / 4 * 4 := by
  rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Mdl.stackRound_eq _ h

end FvModexp

namespace FvModexp

/-- the signed difference `len + nr - cap` of `slices.Grow`'s test (all three below `2^60`) -/
theorem toInt_sub3 (a r c : Nat) (ha : a < 2 ^ 60) (hr : r < 2 ^ 60) (hc : c < 2 ^ 60) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 r - BitVec.ofNat 64 c).toInt = (a : Int) + r - c := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  split <;> omega

end FvModexp
