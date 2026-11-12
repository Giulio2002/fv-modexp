import FvModexp.Proofs.Common.AsmDivNat

/-!
# `divLarge` (natdiv.go:597): the arithmetic of the scaling `shift = nlz(vIn[n-1])` (pure Nat)

`V = lo + B·top` with `B = 2^(64(n-1))`, `lo < B`, `0 < top < 2^64`, `C = 2^clz(top)`:
`V·C < 2^(64 n)` (the scaled divisor fits `n` words, `lshVU`'s carry is 0) and its top word `(V·C) / B ≥ 2^63`
(normalised), and for the dividend `U < 2^(64 m)`: `U·C < 2^(64 (m+1))` with top word `< 2^63` (`2·U·C < 2^(64(m+1))`).
-/

namespace FvModexp.DivLargeMath

theorem scale_lt (lo B top C W : Nat) (hlo : lo < B) (hC : 0 < C) (hW : W = C * (W / C)) (htC : top * C < W) :
    (lo + B * top) * C < B * W := by
  have h1 : top < W / C := by
    rcases Nat.lt_or_ge top (W / C) with h | h
    · exact h
    · exfalso
      have : C * (W / C) ≤ C * top := Nat.mul_le_mul_left _ h
      rw [← hW] at this; rw [Nat.mul_comm] at this; omega
  have h2 : (top + 1) * C ≤ W := by
    rw [hW, Nat.mul_comm C]; exact Nat.mul_le_mul_right _ h1
  have h3 : lo * C < B * C := Nat.mul_lt_mul_of_pos_right hlo hC
  have h4 : B * ((top + 1) * C) ≤ B * W := Nat.mul_le_mul_left _ h2
  calc (lo + B * top) * C = lo * C + B * (top * C) := by rw [Nat.add_mul, Nat.mul_assoc]
    _ < B * C + B * (top * C) := by omega
    _ = B * ((top + 1) * C) := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.add_comm]
    _ ≤ B * W := h4

theorem scale_top (lo B top C : Nat) (hlo : lo < B) (hB : 0 < B) :
    (lo + B * top) * C / B ≥ top * C := by
  apply (Nat.le_div_iff_mul_le hB).2
  have e : (lo + B * top) * C = lo * C + B * (top * C) := by rw [Nat.add_mul, Nat.mul_assoc]
  rw [e, Nat.mul_comm (top * C) B]
  exact Nat.le_add_left _ _

/-- the scaled divisor: `V·2^c < 2^(64 n)` and its top word `≥ 2^63` -/
theorem scale_v (lo top n : Nat) (hlo : lo < 2 ^ (64 * n)) (ht0 : top ≠ 0) (ht : top < 2 ^ 64) :
    (lo + 2 ^ (64 * n) * top) * 2 ^ Janus.Arm64.clzNat 64 top < 2 ^ (64 * (n + 1)) ∧
      2 ^ 63 ≤ (lo + 2 ^ (64 * n) * top) * 2 ^ Janus.Arm64.clzNat 64 top / 2 ^ (64 * n) := by
  obtain ⟨hc63, hlow, hhigh⟩ := AsmDiv.clz_norm64 top ht0 ht
  have hC : 0 < 2 ^ Janus.Arm64.clzNat 64 top := Nat.two_pow_pos _
  have hW : 2 ^ 64 = 2 ^ Janus.Arm64.clzNat 64 top * (2 ^ 64 / 2 ^ Janus.Arm64.clzNat 64 top) := by
    rw [Nat.pow_div (by omega) (by omega), ← Nat.pow_add]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add]
    exact scale_lt lo _ top _ _ hlo hC hW hhigh
  · exact Nat.le_trans hlow (scale_top lo _ top _ hlo (Nat.two_pow_pos _))

/-- the scaled dividend fits one more word with a top word below `2^63`: `2·U·2^c < 2^(64(m+1))` (`c ≤ 63`) -/
theorem scale_u (U m c : Nat) (hU : U < 2 ^ (64 * m)) (hc : c ≤ 63) :
    2 * (U * 2 ^ c) < 2 ^ (64 * (m + 1)) := by
  have h1 : U * 2 ^ c < 2 ^ (64 * m) * 2 ^ c := Nat.mul_lt_mul_of_pos_right hU (Nat.two_pow_pos _)
  have h2 : 2 * 2 ^ c ≤ 2 ^ 64 := by
    rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 ^ (64 * (m + 1)) = 2 ^ (64 * m) * 2 ^ 64 := by
    rw [show 64 * (m + 1) = 64 * m + 64 by omega, Nat.pow_add]
  rw [h3]
  calc 2 * (U * 2 ^ c) < 2 * (2 ^ (64 * m) * 2 ^ c) := by omega
    _ = 2 ^ (64 * m) * (2 * 2 ^ c) := by rw [Nat.mul_left_comm]
    _ ≤ 2 ^ (64 * m) * 2 ^ 64 := Nat.mul_le_mul_left _ h2

end FvModexp.DivLargeMath
