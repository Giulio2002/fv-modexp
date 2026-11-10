import Janus
import FvModexp.Proofs.Common.ExpMont

/-!
# Limb windows of a memory value (agent expmc)

The bridge between the machine view of a Go `nat` (`m.readLE p (8 N)`, little-endian limbs) and the window
operations of the Nat-level models (`FvModexp.Exp.win`, `setWin`, `wd`, ExpMont.lean): reading `z[i:i+n]` is `win`, a
callee that rewrites exactly `z[i:i+n]` turns the value into `setWin`.
-/

namespace FvModexp.Expmc

open Janus Janus.Arm64 FvModexp.Exp

theorem pow256 (k : Nat) : (256 : Nat) ^ (8 * k) = B ^ k := by
  rw [B_def, show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← Nat.pow_mul]; congr 1; omega

theorem readLE_lt_B (m : Memory) (p k : Nat) : m.readLE p (8 * k) < B ^ k := by
  have := Memory.readLE_lt m p (8 * k); rwa [pow256] at this

/-- `[p, p + 8N)` split at limbs `i` and `i + n`. -/
theorem readLE_split3 (m : Memory) (p i n N : Nat) (h : i + n ≤ N) :
    m.readLE p (8 * N) = m.readLE p (8 * i) + B ^ i * m.readLE (p + 8 * i) (8 * n) +
      B ^ (i + n) * m.readLE (p + 8 * (i + n)) (8 * (N - (i + n))) := by
  have e1 : 8 * N = 8 * i + (8 * n + 8 * (N - (i + n))) := by omega
  rw [e1, Memory.readLE_add, Memory.readLE_add, pow256, pow256, Nat.pow_add,
    show p + 8 * i + 8 * n = p + 8 * (i + n) by omega]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]

/-- Reading the window `z[i:i+n]`. -/
theorem readLE_win (m : Memory) (p i n N : Nat) (h : i + n ≤ N) :
    m.readLE (p + 8 * i) (8 * n) = win (m.readLE p (8 * N)) i n := by
  unfold win
  rw [readLE_split3 m p i n N h]
  have hBi : 0 < B ^ i := Nat.pow_pos B_pos
  have hl := readLE_lt_B m p i
  have hw := readLE_lt_B m (p + 8 * i) n
  rw [Nat.pow_add, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ hBi,
    Nat.div_eq_of_lt hl, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

/-- Reading the limb `z[i]`. -/
theorem readLE_wd (m : Memory) (p i N : Nat) (h : i < N) :
    m.readLE (p + 8 * i) 8 = wd (m.readLE p (8 * N)) i := by
  have := readLE_win m p i 1 N (by omega)
  rw [Nat.mul_one] at this; rw [this]; unfold win wd; rw [Nat.pow_one]

/-- A memory that differs from `m` only inside `z[i:i+n]` and holds `v` there: `setWin`. -/
theorem readLE_setWin {m m' : Memory} (p i n N v : Nat) (h : i + n ≤ N)
    (hl : m'.readLE p (8 * i) = m.readLE p (8 * i))
    (hr : m'.readLE (p + 8 * (i + n)) (8 * (N - (i + n))) = m.readLE (p + 8 * (i + n)) (8 * (N - (i + n))))
    (hv : m'.readLE (p + 8 * i) (8 * n) = v) :
    m'.readLE p (8 * N) = setWin (m.readLE p (8 * N)) i n v := by
  unfold setWin
  rw [readLE_split3 m' p i n N h, hl, hr, hv, readLE_split3 m p i n N h]
  have hBi : 0 < B ^ i := Nat.pow_pos B_pos
  have hBin : 0 < B ^ (i + n) := Nat.pow_pos B_pos
  have hl' := readLE_lt_B m p i
  have hw := readLE_lt_B m (p + 8 * i) n
  have hlo : m.readLE p (8 * i) + B ^ i * m.readLE (p + 8 * i) (8 * n) < B ^ (i + n) := by
    rw [Nat.pow_add]
    have : B ^ i * m.readLE (p + 8 * i) (8 * n) + B ^ i ≤ B ^ i * B ^ n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hw
    omega
  have e1 : (m.readLE p (8 * i) + B ^ i * m.readLE (p + 8 * i) (8 * n) +
      B ^ (i + n) * m.readLE (p + 8 * (i + n)) (8 * (N - (i + n)))) % B ^ i = m.readLE p (8 * i) := by
    rw [Nat.pow_add, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hl']
  have e2 : (m.readLE p (8 * i) + B ^ i * m.readLE (p + 8 * i) (8 * n) +
      B ^ (i + n) * m.readLE (p + 8 * (i + n)) (8 * (N - (i + n)))) / B ^ (i + n) =
      m.readLE (p + 8 * (i + n)) (8 * (N - (i + n))) := by
    rw [Nat.add_comm, Nat.mul_add_div hBin, Nat.div_eq_of_lt hlo, Nat.add_zero]
  rw [e1, e2, Nat.mul_comm (B ^ i) v, Nat.mul_comm (B ^ (i + n))]

end FvModexp.Expmc

namespace FvModexp.Expmc
open FvModexp.Exp

theorem B_pow (n : Nat) : B ^ n = 2 ^ (64 * n) := by rw [B_def, ← Nat.pow_mul]

/-- One `nat.montgomery` loop iteration (`montStep`) in terms of the intermediate values a run produces. -/
theorem montStep_eq (n x m k d i Z c w0 v1 c2 Z1 v2 c3 Z2 z1i : Nat)
    (e0 : win Z i n = w0) (e1 : v1 = (w0 + x * d) % B ^ n) (e2 : c2 = (w0 + x * d) / B ^ n)
    (e3 : Z1 = setWin Z i n v1) (e4 : win Z1 i n = v1) (e5 : wd Z1 i = z1i)
    (e6 : v2 = (v1 + m * (z1i * k % B)) % B ^ n) (e7 : c3 = (v1 + m * (z1i * k % B)) / B ^ n)
    (e8 : Z2 = setWin Z1 i n v2) :
    montStep n x m k d i (Z, c) =
      (setWin Z2 (n + i) 1 (((c + c2) % B + c3) % B),
        if (c + c2) % B < c2 ∨ ((c + c2) % B + c3) % B < c3 then 1 else 0) := by
  subst e1 e2 e3 e6 e7 e8
  simp only [montStep]
  rw [e0, e4, e5]

end FvModexp.Expmc

namespace FvModexp.Expmc
open Janus Janus.Arm64 FvModexp.Exp

theorem montIter_c_le (n x y m k : Nat) : ∀ j, (montIter n x y m k j).2 ≤ 1
  | 0 => by simp [montIter]
  | j + 1 => by simp only [montIter, montStep]; split <;> omega

/-- The store `z[n+i] = cy` closes the iteration's value. -/
theorem final_val (m2 : Memory) (zp n i c c2 c3 : Nat) (hi : i < n) :
    (m2.writeLE (zp + (i + n) * 8) 8 (c3 + (c + c2))).readLE zp (8 * (2 * n)) =
      setWin (m2.readLE zp (8 * (2 * n))) (n + i) 1 (((c + c2) % B + c3) % B) := by
  refine readLE_setWin zp (n + i) 1 (2 * n) _ (by omega) ?_ ?_ ?_
  · exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · rw [show zp + 8 * (n + i) = zp + (i + n) * 8 by omega, Nat.mul_one, Memory.readLE_writeLE_self, B_eq]
    omega

theorem succ_reg (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

end FvModexp.Expmc

namespace FvModexp.Expmc
open Janus Janus.Arm64 FvModexp.Exp

/-- The store `z[n+i] = v` with `v ≡ cy (mod 2^64)` closes the iteration's value. -/
theorem final_val_gen (m2 : Memory) (zp n i v cy : Nat) (hi : i < n) (hv : v % 2 ^ 64 = cy) :
    (m2.writeLE (zp + (i + n) * 8) 8 v).readLE zp (8 * (2 * n)) = setWin (m2.readLE zp (8 * (2 * n))) (n + i) 1 cy := by
  refine readLE_setWin zp (n + i) 1 (2 * n) _ (by omega) ?_ ?_ ?_
  · exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · rw [show zp + 8 * (n + i) = zp + (i + n) * 8 by omega, Nat.mul_one, Memory.readLE_writeLE_self]
    rw [← hv]

theorem bv_mul_toNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a * BitVec.ofNat 64 b).toNat = a * b % B := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, B_def]

end FvModexp.Expmc
