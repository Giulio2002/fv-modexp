import FvModexp.Proofs.Common.ExpSlow

set_option autoImplicit false

/-!
# `nat.expNNSlow`: the loop model facts used by the amd64 loop lemmas (agent expmc s79; copy of arm64 SlowMod)

`stepM x m` is `Exp.expNNSlow`'s step verbatim (so `expNNSlow_eq` is `rfl`); `outer_succ1` / `outer_zero1` /
`outer_done1`: one bit, the end of a word, the end of the exponent; `bit63`: the `TBNZ $63` test is the model's digit;
`step_val`: one body (`sqr`, optional `mul`, `div`) is one model step.
-/

namespace FvModexp.Amd64.ExpSlow

/-- `Exp.expNNSlow`'s step -/
def stepM (x m : Nat) : Nat → Nat → Nat := fun z d =>
  let z1 := z * z
  let z2 := if d ≠ 0 then z1 * x else z1
  if m ≠ 0 then z2 % m else z2

theorem expNNSlow_eq (x y m : Nat) :
    Exp.expNNSlow x y m = Exp.outerLoop 1 (stepM x m) y 64 (Exp.nlen y - 1)
      (Exp.wd y (Exp.nlen y - 1) * 2 ^ ((64 - Exp.bitLen (Exp.wd y (Exp.nlen y - 1))) + 1) % Exp.B)
      (64 - ((64 - Exp.bitLen (Exp.wd y (Exp.nlen y - 1))) + 1)) x := rfl

theorem outer_succ1 (st : Nat → Nat → Nat) (Y i yi c z : Nat) :
    Exp.outerLoop 1 st Y 64 i yi (c + 1) z = Exp.outerLoop 1 st Y 64 i ((yi * 2 ^ 1) % Exp.B) c (st z (yi / 2 ^ (64 - 1))) := by
  cases i <;> rfl

theorem outer_zero1 (st : Nat → Nat → Nat) (Y i yi z : Nat) :
    Exp.outerLoop 1 st Y 64 (i + 1) yi 0 z = Exp.outerLoop 1 st Y 64 i (Exp.wd Y i) 64 z := rfl

theorem outer_done1 (st : Nat → Nat → Nat) (Y yi z : Nat) : Exp.outerLoop 1 st Y 64 0 yi 0 z = z := rfl

theorem bit63 (v : BitVec 64) : v.getLsbD 63 = decide (v.toNat / 2 ^ 63 ≠ 0) := by
  have h := v.isLt
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  apply propext
  constructor <;> intro h1 <;> omega

theorem dbl (v : BitVec 64) : (v + v).toNat = v.toNat * 2 ^ 1 % Exp.B := by
  rw [BitVec.toNat_add, Exp.B_def]; congr 1; omega

theorem step_val (X M Zv : Nat) (hM : 0 < M) (v : BitVec 64) :
    (if v.getLsbD 63 = true then Zv * Zv * X else Zv * Zv) % M = stepM X M Zv (v.toNat / 2 ^ (64 - 1)) := by
  rw [bit63]
  simp only [stepM, show M ≠ 0 by omega, ne_eq, not_false_eq_true, ite_true, decide_eq_true_eq]

end FvModexp.Amd64.ExpSlow
