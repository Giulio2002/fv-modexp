import FvModexp.Proofs.Common.DivBasicStep
import FvModexp.Proofs.Common.DivContract
/-!
# List/value lemmas for the `divBasic` loop invariant
-/
namespace FvModexp.Mdl

theorem val_drop_cons (L : List Nat) (k : Nat) : val (L.drop k) = L.getD k 0 + 2 ^ 64 * val (L.drop (k + 1)) := by
  by_cases h : k < L.length
  · rw [List.drop_eq_getElem_cons h, val_cons]
    simp [List.getD_eq_getElem?_getD, h]
  · have h1 : L.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have h2 : L.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have h3 : L.getD k 0 = 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ k)]
    rw [h1, h2, h3]; simp

theorem getD_drop (L : List Nat) (j i : Nat) : (L.drop j).getD i 0 = L.getD (j + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem top3 (L : List Nat) (hL : Wd L) (k : Nat) (hk : k ≤ L.length) (hz : val (L.drop (k + 3)) = 0) :
    ((L.getD (k + 2) 0 * 2 ^ 64 + L.getD (k + 1) 0) * 2 ^ 64 + L.getD k 0) * 2 ^ (64 * k) ≤ val L ∧
    val L < (((L.getD (k + 2) 0 * 2 ^ 64 + L.getD (k + 1) 0) * 2 ^ 64 + L.getD k 0) + 1) * 2 ^ (64 * k) := by
  have h1 := val_split L k hk
  have hlo : val (L.take k) < 2 ^ (64 * k) := by
    have := val_lt (hL.take k)
    simpa [List.length_take, Nat.min_eq_left hk] using this
  have e0 := val_drop_cons L k
  have e1 := val_drop_cons L (k + 1)
  have e2 := val_drop_cons L (k + 2)
  rw [hz] at e2
  have T : ((L.getD (k + 2) 0 * 2 ^ 64 + L.getD (k + 1) 0) * 2 ^ 64 + L.getD k 0) * 2 ^ (64 * k) =
      2 ^ (64 * k) * (L.getD k 0 + 2 ^ 64 * (L.getD (k + 1) 0 + 2 ^ 64 * L.getD (k + 2) 0)) := by grind
  rw [T]
  have hv : val L = val (L.take k) + 2 ^ (64 * k) * (L.getD k 0 + 2 ^ 64 * (L.getD (k + 1) 0 + 2 ^ 64 * L.getD (k + 2) 0)) := by
    rw [h1, e0, e1, e2]; congr 2
  constructor
  · omega
  · have T2 : (((L.getD (k + 2) 0 * 2 ^ 64 + L.getD (k + 1) 0) * 2 ^ 64 + L.getD k 0) + 1) * 2 ^ (64 * k) =
        2 ^ (64 * k) * (L.getD k 0 + 2 ^ 64 * (L.getD (k + 1) 0 + 2 ^ 64 * L.getD (k + 2) 0)) + 2 ^ (64 * k) := by grind
    rw [T2]; omega

/-- The leading limb bounds the value from below. -/
theorem val_ge_top (L : List Nat) : L.getD (L.length - 1) 0 * 2 ^ (64 * (L.length - 1)) ≤ val L := by
  induction L with
  | nil => simp
  | cons d ds ih =>
    cases ds with
    | nil => simp
    | cons e es =>
      simp only [List.length_cons, val_cons, Nat.add_sub_cancel] at *
      have e1 : (d :: e :: es).getD (es.length + 1) 0 = (e :: es).getD es.length 0 := by simp
      have e2 : 64 * (es.length + 1) = 64 * es.length + 64 := by omega
      rw [e1, e2, Nat.pow_add]
      have : (e :: es).getD es.length 0 * 2 ^ (64 * es.length) * 2 ^ 64 ≤ 2 ^ 64 * val (e :: es) := by
        rw [Nat.mul_comm (2 ^ 64)]; exact Nat.mul_le_mul_right _ (by simpa using ih)
      have h3 : (e :: es).getD es.length 0 * (2 ^ (64 * es.length) * 2 ^ 64) =
          (e :: es).getD es.length 0 * 2 ^ (64 * es.length) * 2 ^ 64 := by rw [Nat.mul_assoc]
      omega

theorem val_drop_zero (L : List Nat) (n : Nat) (h : val L < 2 ^ (64 * n)) (hL : Wd L) : val (L.drop n) = 0 := by
  by_cases hn : n ≤ L.length
  · have := val_split L n hn
    have hp : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
    rcases Nat.eq_zero_or_pos (val (L.drop n)) with h0 | hpos
    · exact h0
    · have := Nat.mul_le_mul_left (2 ^ (64 * n)) hpos
      omega
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

theorem top_le (B vn1 vn2 u2 u1 u0 β D X : Nat) (hv2 : vn2 < B)
    (hD2 : D < (vn1 * B + vn2 + 1) * β) (hX1 : ((u2 * B + u1) * B + u0) * β ≤ X) (hXD : X < B * D) : u2 ≤ vn1 := by
  refine Nat.le_of_not_lt (fun h => ?_)
  have h1 : (vn1 + 1) * B * B ≤ (u2 * B + u1) * B + u0 := by
    have a : (vn1 + 1) * B ≤ u2 * B := Nat.mul_le_mul_right _ h
    have b : (vn1 + 1) * B * B ≤ u2 * B * B := Nat.mul_le_mul_right _ a
    have c : u2 * B * B ≤ (u2 * B + u1) * B := by rw [Nat.add_mul]; omega
    omega
  have h2 : (vn1 * B + vn2 + 1) ≤ (vn1 + 1) * B := by
    have : (vn1 + 1) * B = vn1 * B + B := by grind
    omega
  have h3 : (vn1 + 1) * B * B * β ≤ X := Nat.le_trans (Nat.mul_le_mul_right _ h1) hX1
  have h4 : D < (vn1 + 1) * B * β := Nat.lt_of_lt_of_le hD2 (Nat.mul_le_mul_right _ h2)
  have h5 : B * D < B * ((vn1 + 1) * B * β) := by
    have : 0 < B := by
      refine Nat.pos_of_ne_zero (fun h0 => ?_); subst h0; simp at hv2
    exact Nat.mul_lt_mul_of_pos_left h4 this
  have h6 : B * ((vn1 + 1) * B * β) = (vn1 + 1) * B * B * β := by grind
  omega

end FvModexp.Mdl
