import FvModexp.Proofs.Common.NatBasic
/-!
# Slice-update lemmas for the in-place loops of `math/big`

`sl z i n` is the Go slice expression `z[i:i+n]` (as a list); `upd z i l` the store of `l` into it (see `Limbs.lean`).
-/
namespace FvModexp.Mdl

/-- `z[i:i+n]` as a list. -/
def sl (z : List Nat) (i n : Nat) : List Nat := (z.drop i).take n

theorem length_sl (z : List Nat) (i n : Nat) (h : i + n ≤ z.length) : (sl z i n).length = n := by
  simp [sl, List.length_take, List.length_drop]; omega

theorem Wd_sl {z : List Nat} (h : Wd z) (i n : Nat) : Wd (sl z i n) := (h.drop i).take n

theorem drop_upd_far (z l : List Nat) (i j : Nat) (h : i + l.length ≤ z.length) (hj : i + l.length ≤ j) :
    (upd z i l).drop j = z.drop j := by
  unfold upd
  have hA : (z.take i ++ l).length = i + l.length := by simp [List.length_take]; omega
  rw [List.drop_append, List.drop_of_length_le (by omega), List.drop_drop, hA]
  simp only [List.nil_append]
  congr 1; omega

theorem take_upd_near (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) :
    (upd z i l).take i = z.take i := by
  unfold upd
  rw [List.append_assoc, List.take_append_of_le_length (by simp [List.length_take]; omega)]
  simp [List.take_take]

theorem sl_upd_self (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) :
    sl (upd z i l) i l.length = l := by
  unfold sl upd
  have hA : (z.take i).length = i := by simp [List.length_take]; omega
  rw [List.append_assoc, List.drop_append, List.drop_of_length_le (by omega), hA]
  simp only [List.nil_append, Nat.sub_self, List.drop_zero]
  rw [List.take_append_of_le_length (by omega)]
  simp

theorem upd_length' (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) : (upd z i l).length = z.length :=
  length_upd z l i h

end FvModexp.Mdl
