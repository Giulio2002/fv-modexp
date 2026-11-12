import FvModexp.Proofs.Arm64.Nat.DrsCallS
import FvModexp.Proofs.Common.DivRecIdeal

/-!
# `divRecursiveStep` (arm64), loop body: after the recursive call (pure)

`rec_val`: the memory after the call holds the ideal callee's lists (`Mdl.blockR Mdl.recI`): `qhat0` = the quotient
digits, `uu[s:B+n]` = the remainder digits.
`rec_post`: `Ev`, `Fp` (length `l1`), `Bd`, the two lists and the budget after the call, from `DrsPostW`'s parts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the dividend argument of the recursive call as a slice of `U` -/
theorem sl_drop_limbs {M : Memory} {up u1 j B n : Nat} (hB : 1 ≤ B) (hjB : B ≤ j) (hj : j + n ≤ u1) :
    Mdl.sl ((Asm.limbs M up u1).drop (j - B)) (B - 1) (B + n - (B - 1)) = Asm.limbs M (up + 8 * (j - 1)) (n + 1) := by
  have e : Mdl.sl ((Asm.limbs M up u1).drop (j - B)) (B - 1) (B + n - (B - 1)) =
      Mdl.sl (Asm.limbs M up u1) (j - 1) (n + 1) := by
    unfold Mdl.sl; rw [List.drop_drop]; congr 2 <;> omega
  rw [e, Asm.sl_limbs _ _ _ _ _ (by omega)]

theorem drop_limbs_v {M : Memory} {vp n k : Nat} (hk : k ≤ n) :
    (Asm.limbs M vp n).drop k = Asm.limbs M (vp + 8 * k) (n - k) := by
  have : (Asm.limbs M vp n).drop k = Mdl.sl (Asm.limbs M vp n) k (n - k) := by
    unfold Mdl.sl; rw [List.take_of_length_le (by simp)]
  rw [this, Asm.sl_limbs _ _ _ _ _ (by omega)]

/-- **the lists after the recursive call** -/
theorem rec_val {M0 M M' : Memory} {up u1 vp n t0 j : Nat} {U : List Nat} (h40 : 40 ≤ n) (hjB : n / 2 < j)
    (hj : j + n ≤ u1) (huk : Asm.limbs M up u1 = U)
    (hv : M.readLE (vp + 8 * (n / 2 - 1)) (8 * (n - n / 2 + 1)) = M0.readLE (vp + 8 * (n / 2 - 1)) (8 * (n - n / 2 + 1)))
    (hq : natVal M' t0 (n / 2 + 1) =
      natVal M (up + 8 * (j - 1)) (n + 1) / natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1))
    (hr : natVal M' (up + 8 * (j - 1)) (n + 1) =
      natVal M (up + 8 * (j - 1)) (n + 1) % natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1)) :
    Asm.limbs M' t0 (n / 2 + 1) = (Mdl.blockR Mdl.recI (Asm.limbs M0 vp n) n (n / 2) j U).1 ∧
      Asm.limbs M' (up + 8 * (j - 1)) (n + 1) = (Mdl.blockR Mdl.recI (Asm.limbs M0 vp n) n (n / 2) j U).2 := by
  have e1 : Mdl.sl (U.drop (j - n / 2)) (n / 2 - 1) (n / 2 + n - (n / 2 - 1)) = Asm.limbs M (up + 8 * (j - 1)) (n + 1) := by
    rw [← huk]; exact sl_drop_limbs (by omega) (by omega) hj
  have e2 : (Asm.limbs M0 vp n).drop (n / 2 - 1) = Asm.limbs M0 (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1) := by
    rw [drop_limbs_v (by omega), show n - (n / 2 - 1) = n - n / 2 + 1 by omega]
  have ev : Mdl.val (Asm.limbs M0 (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1)) =
      natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1) := by
    rw [Asm.val_limbs]; show M0.readLE _ _ = M.readLE _ _; exact hv.symm
  unfold Mdl.blockR Mdl.recI
  rw [e1, e2, Asm.val_limbs, ev]
  simp only [List.length_replicate, Asm.length_limbs]
  refine ⟨?_, ?_⟩
  · rw [Mdl.eq_toL (Asm.Wd_limbs M' t0 (n / 2 + 1)), Asm.val_limbs, Asm.length_limbs]
    exact congrArg (Mdl.toL · (n / 2 + 1)) hq
  · rw [Mdl.eq_toL (Asm.Wd_limbs M' _ (n + 1)), Asm.val_limbs, Asm.length_limbs]
    exact congrArg (Mdl.toL · (n + 1)) hr

end FvModexp.Arm64.DivRec
