import FvModexp.Proofs.Arm64.Exp.W4Mid
import FvModexp.Proofs.Common.ExpOddCore
import FvModexp.Proofs.Common.ExpEven

/-!
# window-4 (arm64): the value of the result

The machine chain computes `if m ≤ zz then 0 else zz` with `zz = montgomery(zjVal …, 1)` (`W4Tail.TailPost`,
`W4ExitS.JoinPost`) from the normalised `x` value `Xv' ≡ x (mod m)`, `RR = 2^(128n) mod m` and
`k0 = (2^64 - newton(m0)) mod 2^64`; `w4_value` shows it is `x^y mod m` (`Exp.winMont_core`).
-/

open Janus Janus.Arm64 FvModexp

namespace FvModexp.Arm64.W4Pro

/-- the value of `y[0:ylen]` is at least `B^(ylen-1)` when its top word is not zero -/
theorem y_ge (M : Memory) (yp ylen : Nat) (hyl : 0 < ylen) (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 ≠ 0) :
    Exp.B ^ (ylen - 1) ≤ M.readLE yp (8 * ylen) := by
  have e := M.readLE_add yp (8 * (ylen - 1)) 8
  rw [show 8 * (ylen - 1) + 8 = 8 * ylen by omega] at e
  have hp : (256 : Nat) ^ (8 * (ylen - 1)) = Exp.B ^ (ylen - 1) := by
    rw [Nat.pow_mul, Exp.B_def, show (256 : Nat) ^ 8 = 2 ^ 64 by rfl]
  rw [e, hp]
  have : 1 ≤ M.readLE (yp + 8 * (ylen - 1)) 8 := Nat.pos_of_ne_zero hyi
  have h2 : Exp.B ^ (ylen - 1) * 1 ≤ Exp.B ^ (ylen - 1) * M.readLE (yp + 8 * (ylen - 1)) 8 :=
    Nat.mul_le_mul_left _ this
  omega

theorem k0_eq (m0 : Nat) : (2 ^ 64 - Exp.newton 64 m0) % 2 ^ 64 = Exp.montK0 m0 := by
  have h : Exp.newton 64 m0 < Exp.B := by
    unfold Exp.newton; exact Exp.newton_lt 64 0 _ _ (Nat.mod_lt _ Exp.B_pos)
  unfold Exp.montK0
  rw [Exp.B_def] at h ⊢; rw [Nat.mod_eq_of_lt h]

theorem zjVal_eq (n Mv k0 : Nat) (tbl : Nat → Nat) (Y ylen : Nat) :
    zjVal n Mv k0 tbl Y ylen (Exp.wd Y (ylen - 1)) =
      Exp.winRun 4 (fun z d => Exp.montgomery n (Exp.iter (fun z => Exp.montgomery n z z Mv k0) 4 z) (tbl d) Mv k0)
        tbl Y (ylen - 1) (Exp.wd Y (ylen - 1)) := by
  unfold zjVal Exp.winRun
  simp only [Exp.B_def]

/-- **the value of window-4's result** -/
theorem w4_value (n Mv X Xv' Y ylen : Nat) (hn : 0 < n) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1)
    (hXm : Xv' % Mv = X % Mv) (hXB : Xv' < Exp.B ^ n) (hyl : 0 < ylen) (hYB : Y < Exp.B ^ ylen)
    (hYg : Exp.B ^ (ylen - 1) ≤ Y) :
    (if Mv ≤ Exp.montgomery n (zjVal n Mv ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64)
        (Exp.montPow n Mv ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64) Xv' (2 ^ (128 * n) % Mv))
        Y ylen (Exp.wd Y (ylen - 1))) 1 Mv ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64)
      then 0 else Exp.montgomery n (zjVal n Mv ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64)
        (Exp.montPow n Mv ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64) Xv' (2 ^ (128 * n) % Mv))
        Y ylen (Exp.wd Y (ylen - 1))) 1 Mv ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64)) = X ^ Y % Mv := by
  rw [k0_eq, zjVal_eq, show (2 : Nat) ^ (128 * n) = Exp.B ^ (2 * n) by
    rw [Exp.B_def, ← Nat.pow_mul]; congr 1; omega]
  obtain ⟨h1, h2⟩ := Exp.winMont_core 4 (Or.inr rfl) n Mv (Exp.montK0 (Mv % Exp.B)) X Xv' Y (ylen - 1) hn hmB hMo
    (Exp.montK0_hk Mv hMo) hXB hXm (by rwa [show ylen - 1 + 1 = ylen by omega]) hYg
  generalize Exp.montgomery n _ 1 Mv (Exp.montK0 (Mv % Exp.B)) = zz at h1 h2 ⊢
  by_cases h : Mv ≤ zz
  · rw [if_pos h]
    have : zz = Mv := by omega
    rw [this, Nat.mod_self] at h2; exact h2
  · rw [if_neg h, ← h2, Nat.mod_eq_of_lt (by omega)]

end FvModexp.Arm64.W4Pro
