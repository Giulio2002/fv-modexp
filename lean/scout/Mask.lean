import Janus
theorem sshr63_allOnes (v : BitVec 64) (h : 2 ^ 63 ≤ v.toNat) : v.sshiftRight 63 = BitVec.allOnes 64 := by
  have hm : v.msb = true := by
    rw [BitVec.msb_eq_decide]; simp; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hr : (BitVec.allOnes 64).getLsbD i = true := by rw [BitVec.getLsbD_allOnes]; simp [hi]
  rw [hr]
  rcases Nat.eq_zero_or_pos i with rfl | hp
  · rw [BitVec.msb_eq_getLsbD_last] at hm; simpa using hm
  · have : ¬ (63 + i < 64) := by omega
    simp [this, show ¬ 64 ≤ i by omega, hm]
example (a b : Nat) (ha : a < b) (hb : b < 2 ^ 63) : 2 ^ 63 ≤ (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
