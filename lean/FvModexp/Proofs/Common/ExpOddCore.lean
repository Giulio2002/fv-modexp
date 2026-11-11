import FvModexp.Proofs.Common.ExpOdd
/-
  ExpOddCore: the core of `expNNOddMont_correct` (ExpOdd.lean) for any representative `x1 ≡ x (mod m)` with
  `x1 < B^n` and any word count `n` with `m < B^n` (the machine proof of window-4 has the normalised `x` and `len m`
  as given numbers). Proof adapted from `expNNOddMont_correct`.
-/
namespace FvModexp.Exp

theorem winMont_core (w : Nat) (hw : w = 2 ∨ w = 4) (n m k x x1 y i : Nat) (hn1 : 1 ≤ n) (hmB : m < B ^ n)
    (hm : m % 2 = 1) (hk : (k * m + 1) % B = 0) (hx1B : x1 < B ^ n) (hx1m : x1 % m = x % m)
    (hyB : y < B ^ (i + 1)) (hyge : B ^ i ≤ y) :
    montgomery n (winRun w (fun z d => montgomery n (iter (fun z => montgomery n z z m k) w z)
      (montPow n m k x1 (B ^ (2 * n) % m) d) m k) (montPow n m k x1 (B ^ (2 * n) % m)) y i (wd y i)) 1 m k ≤ m ∧
    montgomery n (winRun w (fun z d => montgomery n (iter (fun z => montgomery n z z m k) w z)
      (montPow n m k x1 (B ^ (2 * n) % m) d) m k) (montPow n m k x1 (B ^ (2 * n) % m)) y i (wd y i)) 1 m k % m =
      x ^ y % m := by
  have hw0 : 0 < w := by omega
  have hK : 64 / w * w = 64 := by rcases hw with rfl | rfl <;> decide
  have hw64 : w ≤ 64 := by omega
  have hm0 : 0 < m := by omega
  obtain ⟨RR, hRRd⟩ : ∃ RR, RR = B ^ (2 * n) % m := ⟨_, rfl⟩
  rw [← hRRd]
  have hRRB : RR < B ^ n := by rw [hRRd]; exact Nat.lt_trans (Nat.mod_lt _ hm0) hmB
  have hco := coprime_B_pow_odd n m hm
  have hBB : B ^ (2 * n) = B ^ n * B ^ n := by rw [Nat.two_mul, Nat.pow_add]
  -- table
  have htbl : ∀ d, MRep n m x1 (montPow n m k x1 RR d) d := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      match d, ih with
      | 0, _ =>
        obtain ⟨h1, h2⟩ := mont_rep n m k 1 RR hn1 (by
          have : 1 < B ^ n := by
            have := Nat.pow_le_pow_right B_pos hn1
            have h3 : 1 < B := by rw [B_def]; decide
            simp at this; omega
          omega) hRRB hmB hk
        refine ⟨h1, ?_⟩
        simp only [montPow]
        apply cg_cancel (R := B ^ n) hco
        rw [h2, hRRd, Nat.one_mul, Nat.mod_mod, hBB]
        simp
      | 1, _ =>
        obtain ⟨h1, h2⟩ := mont_rep n m k x1 RR hn1 hx1B hRRB hmB hk
        refine ⟨h1, ?_⟩
        simp only [montPow]
        apply cg_cancel (R := B ^ n) hco
        rw [h2, hRRd, Nat.mul_mod_mod, hBB, Nat.pow_one]
        congr 1; grind
      | i + 2, ih =>
        have h1 := ih (i + 1) (by omega)
        have h' := ih 1 (by omega)
        simp only [montPow] at h' ⊢
        exact mont_mul_rep n m k x1 hn1 hmB hm hk (e := i + 1) (e' := 1) h1 h'
  have hstep : StepOk w (MRep n m x1)
      (fun z d => montgomery n (iter (fun z => montgomery n z z m k) w z) (montPow n m k x1 RR d) m k) := by
    intro z e d _ hz
    exact mont_mul_rep n m k x1 hn1 hmB hm hk (msq_iter_rep n m k x1 hn1 hmB hm hk w z e hz) (htbl d)
  have hBi : 0 < B ^ i := Nat.pow_pos B_pos
  have hyi0 : 0 < wd y i := by
    unfold wd
    have h1 : 1 ≤ y / B ^ i := (Nat.le_div_iff_mul_le hBi).mpr (by omega)
    have h2 : y / B ^ i < B := by
      rw [Nat.div_lt_iff_lt_mul hBi, Nat.mul_comm]
      have h := hyB; rw [Nat.pow_succ] at h; exact h
    rw [Nat.mod_eq_of_lt h2]; omega
  have hrun := winRun_rep w (MRep n m x1) _ hw0 hK hw64 hstep (montPow n m k x1 RR)
    (fun d _ => htbl d) y i (wd y i) hyi0 (wd_lt y i)
  have hexp : wd y i * B ^ i + y % B ^ i = y := by
    unfold wd
    have := Nat.mod_mul (a := B ^ i) (b := B) (x := y)
    rw [← Nat.pow_succ, Nat.mod_eq_of_lt hyB] at this
    grind
  rw [hexp] at hrun
  obtain ⟨z, hzd⟩ : ∃ z, z = winRun w
      (fun z d => montgomery n (iter (fun z => montgomery n z z m k) w z) (montPow n m k x1 RR d) m k)
      (montPow n m k x1 RR) y i (wd y i) := ⟨_, rfl⟩
  rw [← hzd] at hrun ⊢
  obtain ⟨zz, hzz⟩ : ∃ zz, zz = montgomery n z 1 m k := ⟨_, rfl⟩
  rw [← hzz]
  obtain ⟨hz1, hz2⟩ := hrun
  obtain ⟨hr1, hr2⟩ := mont_rep n m k z 1 hn1 hz1 (by
    have := Nat.pow_le_pow_right B_pos hn1
    have h3 : 1 < B := by rw [B_def]; decide
    simp at this; omega) hmB hk
  obtain ⟨Q, T, hQ, hT, hTlt, hr⟩ := montgomery_spec n z 1 m k hn1 hz1 (by
    have := Nat.pow_le_pow_right B_pos hn1
    have h3 : 1 < B := by rw [B_def]; decide
    simp at this; omega) hmB hk
  have hTle : T ≤ m := by
    have h1 : z * 1 + Q * m < B ^ n * (m + 1) := by
      have := mac_lt (B ^ n) (m + 1) (z * 1) Q m (by omega) hQ (by omega); exact this
    have h2 : T * B ^ n < (m + 1) * B ^ n := by rw [hT, Nat.mul_comm (m + 1)]; exact h1
    have := Nat.lt_of_mul_lt_mul_right h2
    omega
  have hzzT : zz = T := by
    rw [hzz, hr, if_neg (by omega)]
  have hzzm : zz % m = x ^ y % m := by
    have h1 : zz * B ^ n % m = x1 ^ y * B ^ n % m := by
      rw [hzz, hr2, Nat.mul_one]; exact hz2
    have := cg_cancel hco h1
    rw [this, Nat.pow_mod, hx1m, ← Nat.pow_mod]
  refine ⟨by omega, hzzm⟩

end FvModexp.Exp
