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
