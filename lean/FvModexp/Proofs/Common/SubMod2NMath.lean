import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.SetBytesMath
import FvModexp.Proofs.Common.ExpEven

/-!
# Word-level facts for the machine-code proof of `nat.subMod2N` (nat.go:1726), ISA-independent (agent infra)

* `norm_nlen`: a normalised nat of `l` limbs has `nlen` (the word count of its value) `l`;
* `cmp_lt_iff`: `x.cmp(y) < 0` (lengths first, then the value) is the numeric `X < Y` for normalised operands;
* `compl_step`: one step of the loop `for i := range z { z[i] = ^z[i] }` (nat.go:1751) on the low `i` limbs;
* `subMod2N_lt_eq`: the value of the `x < y` branch, as computed by the machine (`B^W - 1 - d`, truncated, `+ 1`).
-/

open Janus Janus.Arm64 Janus.Spec FvModexp FvModexp.Exp

namespace FvModexp.SubMod2N

theorem natVal_lower (m : Memory) (p l : Nat) (h : NatNorm m p l) (hl : 0 < l) :
    2 ^ (64 * (l - 1)) ≤ natVal m p l := by
  rcases h with h | h
  · omega
  · have e := natVal_succ m p (l - 1)
    rw [Nat.sub_add_cancel hl] at e
    rw [e]
    have : 1 ≤ m.readLE (p + 8 * (l - 1)) 8 := Nat.pos_of_ne_zero h
    have := Nat.mul_le_mul_left (2 ^ (64 * (l - 1))) this
    omega

theorem Bpow (n : Nat) : B ^ n = 2 ^ (64 * n) := by
  unfold B; rw [← Nat.pow_mul]

theorem norm_nlen (m : Memory) (p l : Nat) (h : NatNorm m p l) : nlen (natVal m p l) = l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [nlen]
  · have h1 := natVal_lower m p l h hl
    have h2 := natVal_lt m p l
    apply Nat.le_antisymm
    · exact nlen_le_iff.2 (by rw [Bpow]; exact h2)
    · have hpos : 0 < natVal m p l := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) h1
      refine Nat.not_lt.1 fun hc => ?_
      have : nlen (natVal m p l) ≤ l - 1 := by omega
      have := nlen_le_iff.1 this
      rw [Bpow] at this
      omega

/-- the comparison of two normalised nats by length first is the numeric comparison -/
theorem cmp_lt_iff (m : Memory) (x xl y yl : Nat) (hx : NatNorm m x xl) (hy : NatNorm m y yl) :
    (xl < yl ∨ (xl = yl ∧ natVal m x xl < natVal m y yl)) ↔ natVal m x xl < natVal m y yl := by
  constructor
  · rintro (h | ⟨_, h⟩)
    · have h1 := natVal_lower m y yl hy (by omega)
      have h2 := natVal_lt m x xl
      have : 2 ^ (64 * xl) ≤ 2 ^ (64 * (yl - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact h
  · intro h
    rcases Nat.lt_trichotomy xl yl with h' | rfl | h'
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, h⟩
    · exfalso
      have h1 := natVal_lower m x xl hx (by omega)
      have h2 := natVal_lt m y yl
      have : 2 ^ (64 * yl) ≤ 2 ^ (64 * (xl - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-- one complement step: the low `i + 1` limbs after `z[i] = ^z[i]` -/
theorem compl_step (m : Memory) (p i D w : Nat) (hD : natVal m p i = 2 ^ (64 * i) - 1 - D)
    (hDl : D < 2 ^ (64 * i)) (hw : w < 2 ^ 64) :
    natVal (m.writeLE (p + 8 * i) 8 (2 ^ 64 - 1 - w)) p (i + 1) = 2 ^ (64 * (i + 1)) - 1 - (D + 2 ^ (64 * i) * w) := by
  rw [natVal_store_top _ _ _ _ (by omega), hD]
  have e : 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := by rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  rw [e]
  have h1 : 2 ^ (64 * i) * w ≤ 2 ^ (64 * i) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 ^ (64 * i) * (2 ^ 64 - 1 - w) = 2 ^ (64 * i) * (2 ^ 64 - 1) - 2 ^ (64 * i) * w := by
    rw [Nat.mul_sub]
  have h3 : 2 ^ (64 * i) * 2 ^ 64 = 2 ^ (64 * i) * (2 ^ 64 - 1) + 2 ^ (64 * i) := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : 2 ^ (64 * i) ≤ 2 ^ (64 * i) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [h2, h3]
  omega

/-- the value of the `x < y` branch of `subMod2N` as the machine computes it, for `0 < d < 2^n`, `W = ⌈n/64⌉` -/
theorem lt_branch (x y n d : Nat) (_hn : 0 < n) (hd : d = y % 2 ^ n - x % 2 ^ n) (hlt : x % 2 ^ n < y % 2 ^ n) :
    subMod2N x y n = (B ^ ((n + 63) / 64) - 1 - d) % 2 ^ n + 1 := by
  unfold subMod2N
  simp only [trunc_if_eq]
  rw [ite_eq_right (by omega)]
  have hdl : d < 2 ^ n := by have := Nat.mod_lt y (Nat.two_pow_pos n); omega
  have : nlen d ≤ (n + 63) / 64 := by
    apply nlen_le_iff.2
    rw [Bpow]
    exact Nat.lt_of_lt_of_le hdl (Nat.pow_le_pow_right (by omega) (by omega))
  rw [show max (nlen (y % 2 ^ n - x % 2 ^ n)) ((n + 63) / 64) = (n + 63) / 64 by rw [← hd]; omega, ← hd]

theorem ge_branch (x y n : Nat) (hge : y % 2 ^ n ≤ x % 2 ^ n) :
    subMod2N x y n = x % 2 ^ n - y % 2 ^ n := by
  unfold subMod2N
  simp only [trunc_if_eq]
  rw [ite_eq_left hge]

end FvModexp.SubMod2N
