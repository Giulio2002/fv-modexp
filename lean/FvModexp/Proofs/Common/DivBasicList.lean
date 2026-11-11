import FvModexp.Proofs.Common.AsmModel
import FvModexp.Proofs.Common.DivBasicMem

/-!
# `divBasic`: list-level versions of the asm kernels' value statements (for windows read in different memories)
-/

namespace FvModexp.Asm

/-- `subVV` from its value equation -/
theorem subVV_list (X Y Z : List Nat) (b : Nat) (hX : Mdl.Wd X) (hY : Mdl.Wd Y) (hZ : Mdl.Wd Z)
    (hl1 : Y.length = X.length) (hl2 : Z.length = X.length) (_hb : b ≤ 1)
    (h : Mdl.val Z + Mdl.val Y = Mdl.val X + 2 ^ (64 * X.length) * b) :
    Z = (Mdl.subVV X Y).1 ∧ b = (Mdl.subVV X Y).2 := by
  obtain ⟨hl, hw, -, hv⟩ := Mdl.subVVc_spec X Y 0 hX hY hl1.symm (by omega)
  have hR := Mdl.val_lt hw
  have hZl := Mdl.val_lt hZ
  rw [hl] at hR; rw [hl2] at hZl
  have e : Mdl.val Z + 2 ^ (64 * X.length) * (Mdl.subVVc X Y 0).2 =
      Mdl.val (Mdl.subVVc X Y 0).1 + 2 ^ (64 * X.length) * b := by omega
  obtain ⟨e1, e2⟩ := split_unique hZl hR e
  exact ⟨eq_of_val hZ hw (by rw [hl2]; exact hl.symm) e1, e2.symm⟩

/-- `addVV` from its value equation -/
theorem addVV_list (X Y Z : List Nat) (c : Nat) (hX : Mdl.Wd X) (hY : Mdl.Wd Y) (hZ : Mdl.Wd Z)
    (hl1 : Y.length = X.length) (hl2 : Z.length = X.length)
    (h : Mdl.val Z + 2 ^ (64 * X.length) * c = Mdl.val X + Mdl.val Y) :
    Z = (Mdl.addVV X Y).1 ∧ c = (Mdl.addVV X Y).2 := by
  obtain ⟨hl, hw, -, hv⟩ := Mdl.addVVc_spec X Y 0 hX hY hl1.symm (by omega)
  have hR := Mdl.val_lt hw
  have hZl := Mdl.val_lt hZ
  rw [hl] at hR; rw [hl2] at hZl
  obtain ⟨e1, e2⟩ := split_unique hZl hR (c := c) (c' := (Mdl.addVVc X Y 0).2) (by omega)
  exact ⟨eq_of_val hZ hw (by rw [hl2]; exact hl.symm) e1, e2⟩

end FvModexp.Asm
