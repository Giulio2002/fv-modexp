import FvModexp.Proofs.Common.Conv

/-!
# The arithmetic of `basicSqr` (natmul.go:113)

For the limbs `f j` of `x` (`pre f i = x[0:i]` as a number, `B = 2^64`):
* `sqS f i = Σ_{j<i} f j² · B^(2j)` — what `z[0:2i]` holds after the squares of the first `i` limbs;
* `sqT f i = Σ_{j<i} f j · x[0:j] · B^j` — what `t[0:2i]` holds after the cross products of the first `i` limbs;
* `sq_id : sqS f n + 2 · sqT f n = x[0:n]²` (`(a + d B^j)² = a² + 2 d a B^j + d² B^(2j)`),
* `sqT_lt`: `sqT f (i+1) < B^(2i+1)` (the top word `t[2n-1]` is zero before the doubling), `sqT_mod`: `B ∣ sqT f i`.
-/

namespace FvModexp.SqrMath

/-- `x[0:i]` as a number. -/
def pre (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => pre f i + f i * 2 ^ (64 * i)

def sqS (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => sqS f i + f i * f i * 2 ^ (64 * (2 * i))

def sqT (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => sqT f i + f i * pre f i * 2 ^ (64 * i)

theorem sq_id (f : Nat → Nat) (n : Nat) : sqS f n + 2 * sqT f n = pre f n * pre f n := by
  induction n with
  | zero => rfl
  | succ i ih =>
    simp only [sqS, sqT, pre]
    have e : (2 : Nat) ^ (64 * (2 * i)) = 2 ^ (64 * i) * 2 ^ (64 * i) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [e]
    generalize pre f i = P at *
    generalize f i = F
    generalize 2 ^ (64 * i) = Q
    have h1 : (P + F * Q) * (P + F * Q) = P * P + 2 * (F * P * Q) + F * F * (Q * Q) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have a1 : P * (F * Q) = F * P * Q := by ac_rfl
      have a2 : F * Q * P = F * P * Q := by ac_rfl
      have a3 : F * Q * (F * Q) = F * F * (Q * Q) := by ac_rfl
      rw [a1, a2, a3]; omega
    rw [h1, ← ih]; omega

theorem pre_lt (f : Nat → Nat) (hf : ∀ j, f j < 2 ^ 64) (i : Nat) : pre f i < 2 ^ (64 * i) := by
  induction i with
  | zero => simp [pre]
  | succ i ih =>
    simp only [pre]
    have e : (2 : Nat) ^ (64 * (i + 1)) = 2 ^ 64 * 2 ^ (64 * i) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e]
    have h1 : (f i + 1) * 2 ^ (64 * i) ≤ 2 ^ 64 * 2 ^ (64 * i) := Nat.mul_le_mul_right _ (hf i)
    rw [Nat.succ_mul] at h1
    omega

theorem sqT_lt (f : Nat → Nat) (hf : ∀ j, f j < 2 ^ 64) (i : Nat) : sqT f (i + 1) < 2 ^ (64 * (2 * i + 1)) := by
  induction i with
  | zero =>
    show sqT f 1 < 2 ^ 64
    simp only [sqT, pre, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]; exact Nat.two_pow_pos 64
  | succ i ih =>
    rw [sqT]
    have hp := pre_lt f hf (i + 1)
    have hd := hf (i + 1)
    have e1 : (2 : Nat) ^ (64 * (2 * (i + 1) + 1)) = 2 ^ 64 * (2 ^ (64 * (i + 1)) * 2 ^ (64 * (i + 1))) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    have e2 : (2 : Nat) ^ (64 * (i + 1)) * 2 ^ (64 * (i + 1)) = 2 ^ 64 * 2 ^ (64 * (2 * i + 1)) := by
      rw [← Nat.pow_add, ← Nat.pow_add, show 64 * (i + 1) + 64 * (i + 1) = 64 + 64 * (2 * i + 1) by omega]
    have h1 : f (i + 1) * pre f (i + 1) ≤ (2 ^ 64 - 1) * 2 ^ (64 * (i + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : f (i + 1) * pre f (i + 1) * 2 ^ (64 * (i + 1)) ≤ (2 ^ 64 - 1) * (2 ^ (64 * (i + 1)) * 2 ^ (64 * (i + 1))) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h1
    rw [e1, e2] at *
    generalize f (i + 1) * pre f (i + 1) * 2 ^ (64 * (i + 1)) = A at *
    generalize 2 ^ (64 * (2 * i + 1)) = C at *
    omega

theorem sqT_mod (f : Nat → Nat) (i : Nat) : sqT f i % 2 ^ 64 = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [sqT]
    cases i with
    | zero => simp [sqT, pre]
    | succ k =>
      have e : (2 : Nat) ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, Nat.add_mod, ih, show f (k + 1) * pre f (k + 1) * (2 ^ 64 * 2 ^ (64 * k)) =
        2 ^ 64 * (f (k + 1) * pre f (k + 1) * 2 ^ (64 * k)) by ac_rfl, Nat.mul_mod_right]

/-! ## Memory bridge -/

open Janus Janus.Arm64

/-- the limbs of the array at `p` -/
@[reducible] def lim (m : Memory) (p : Nat) : Nat → Nat := fun j => m.readLE (p + 8 * j) 8

theorem lim_lt (m : Memory) (p : Nat) : ∀ j, lim m p j < 2 ^ 64 := fun j => by
  have := Memory.readLE_lt m (p + 8 * j) 8; simpa using this

theorem natVal_eq_pre (m : Memory) (p n : Nat) : natVal m p n = pre (lim m p) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natVal_succ, ih, pre, Nat.mul_comm (lim m p n)]

end FvModexp.SqrMath
