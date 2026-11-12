import FvModexp.Proofs.Common.DivRec
/-!
# The ideal callees of `divRecursiveStep`'s model (`recI`, `mulI`)

The machine proof of `divRecursiveStep` (Arm64/Nat/Drs*.lean) instantiates the model's callee parameters with the unique
functions the machine summaries determine: the recursive step writes `z = u / v` and `u = u mod v` in place (lengths
kept), `nat.mul` returns the normalised product. `toL x n` = the `n` base-`2^64` digits of `x`.
`recI_ok : RecOk recI N` and `mulI_ok : MulContract mulI`.
-/
namespace FvModexp.Mdl

/-- the `n` least significant base-`2^64` digits of `x` -/
def toL (x : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => x % 2 ^ 64 :: toL (x / 2 ^ 64) n

@[simp] theorem length_toL (x n : Nat) : (toL x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [toL, ih]

theorem Wd_toL (x n : Nat) : Wd (toL x n) := by
  induction n generalizing x with
  | zero => intro d hd; simp [toL] at hd
  | succ n ih =>
    intro d hd
    simp only [toL, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · exact ih _ d hd

theorem val_toL (x n : Nat) : val (toL x n) = x % 2 ^ (64 * n) := by
  induction n generalizing x with
  | zero => simp [toL, Nat.mod_one]
  | succ n ih =>
    simp only [toL, val_cons, ih]
    rw [show 64 * (n + 1) = 64 + 64 * n by omega, Nat.pow_add, Nat.mod_mul]

/-- a word list is the digit list of its value -/
theorem eq_toL {l : List Nat} (h : Wd l) : l = toL (val l) l.length := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    have h' := Wd_cons.1 h
    simp only [toL, List.length_cons, val_cons]
    have hd : d < 2 ^ 64 := h'.1
    congr 1
    · omega
    · rw [show (d + 2 ^ 64 * val ds) / 2 ^ 64 = val ds by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hd]; simp]
      exact ih h'.2

/-- the ideal recursive step: quotient into `z`'s length, remainder into `u`'s -/
def recI (z u v : List Nat) : List Nat × List Nat :=
  (toL (val u / val v) z.length, toL (val u % val v) u.length)

/-- the ideal multiplier: the normalised product -/
def mulI (a b : List Nat) : List Nat := norm (toL (val a * val b) (a.length + b.length))

theorem mulI_ok : MulContract mulI := by
  intro a b ha hb
  have hab : val a * val b < 2 ^ (64 * (a.length + b.length)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (val_lt ha) (val_lt hb)
  refine ⟨Wd_norm (Wd_toL _ _), ?_, normed_norm _, ?_⟩
  · unfold mulI; rw [val_norm, val_toL, Nat.mod_eq_of_lt hab]
  · have := length_norm_le (toL (val a * val b) (a.length + b.length))
    rw [length_toL] at this; unfold mulI; exact this

theorem recI_ok (N : Nat) : RecOk recI N := by
  intro z u v _ _ hu hv h2 htop _ hH
  have hne : v ≠ [] := by intro e; subst e; simp at h2
  have hvge := val_ge_top63 hne htop
  have hvlt := val_lt hv
  have hvp : 0 < val v := by
    have : 0 < 2 ^ 63 * 2 ^ (64 * (v.length - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    omega
  have hq : val u / val v < 2 ^ (64 * z.length) := by
    refine (Nat.div_lt_iff_lt_mul hvp).2 ?_
    have e : 2 ^ (64 * (v.length + z.length)) = 2 * (2 ^ 63 * 2 ^ (64 * (v.length - 1)) * 2 ^ (64 * z.length)) := by
      rw [show 64 * (v.length + z.length) = 1 + (63 + (64 * (v.length - 1) + 64 * z.length)) by omega,
        Nat.pow_add, Nat.pow_add, Nat.pow_add]; simp only [Nat.pow_one, Nat.mul_assoc]
    have := Nat.mul_le_mul_right (2 ^ (64 * z.length)) hvge
    rw [Nat.mul_comm (2 ^ (64 * z.length))]; omega
  have hr : val u % val v < 2 ^ (64 * u.length) := Nat.lt_of_le_of_lt (Nat.mod_le _ _) (val_lt hu)
  have hrv : val u % val v < 2 ^ (64 * v.length) := Nat.lt_trans (Nat.mod_lt _ hvp) hvlt
  refine ⟨by simp [recI], by simp [recI], Wd_toL _ _, Wd_toL _ _, ?_, ?_, ?_⟩
  · simp only [recI]; rw [val_toL, Nat.mod_eq_of_lt hq]
  · simp only [recI]; rw [val_toL, Nat.mod_eq_of_lt hr]
  · refine zero_drop_of_lt (Wd_toL _ _) ?_
    show val (toL (val u % val v) u.length) < _
    rw [val_toL, Nat.mod_eq_of_lt hr]; exact hrv

end FvModexp.Mdl
