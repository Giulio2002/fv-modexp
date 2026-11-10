import FvModexp.Proofs.Common.DivRecLoop
/-!
# Spec of the final block of `divRecursiveStep` (natdiv.go:845-892)
-/
namespace FvModexp.Mdl

theorem lt_of_drop_zero {u : List Nat} (hu : Wd u) {k : Nat} (h : ∀ d ∈ u.drop k, d = 0) : val u < 2 ^ (64 * k) := by
  have h1 := (val_take_mod u k hu).2
  have h2 : val (u.drop k) = 0 := val_eq_zero_iff.2 h
  rw [h2] at h1
  refine Nat.lt_of_not_ge ?_
  intro hge
  have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos (64 * k))).2 (by simpa using hge : 1 * 2 ^ (64 * k) ≤ val u)
  omega

theorem finalBlock_spec (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (N : Nat) (hrec : RecOk rec N)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul)
    (v : List Nat) (n B m lz U0 j : Nat) (z u : List Nat)
    (hv : Wd v) (hvn : v.length = n) (htop : 2 ^ 63 ≤ topLimb v) (hB1 : 1 ≤ B) (h2B : 2 * B ≤ n) (hnN : n - (B - 1) ≤ N)
    (hI : LI v n B m lz U0 j z u) (hjB : j ≤ B) (hU0 : U0 < val v * 2 ^ (64 * lz)) :
    (finalBlock rec mul v n B z u).1.length = lz ∧ (finalBlock rec mul v n B z u).2.length = m + n ∧
    Wd (finalBlock rec mul v n B z u).1 ∧ Wd (finalBlock rec mul v n B z u).2 ∧
    val (finalBlock rec mul v n B z u).1 = U0 / val v ∧ val (finalBlock rec mul v n B z u).2 = U0 % val v ∧
    (∀ d ∈ (finalBlock rec mul v n B z u).2.drop n, d = 0) ∧
    (finM rec mul v n B u).c = 0 ∧ (finM rec mul v n B u).e ≤ 0 ∧
    (norm (finR rec v B u).1).length + (B - 1) ≤ 3 * n ∧ (norm (finM rec mul v n B u).q).length ≤ lz := by
  obtain ⟨hz, hu, hzl, hul, hval, hbd, htail, hjm⟩ := hI
  have hsB : B - 1 + 1 = B := by omega
  have hsn : B - 1 < n := by omega
  have hvp : 0 < val v := by
    have cx : Ctx v n (B - 1) B 0 n := ⟨hv, hvn, htop, hsB, h2B, by omega, Nat.le_refl _⟩
    have := cx.v1S_ge
    have : 0 < 2 ^ 63 * 2 ^ (64 * (n - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    have := cx.v_split
    omega
  have hvlt : val v < 2 ^ (64 * n) := by have := val_lt hv; rwa [hvn] at this
  -- bound on u
  have htail' : ∀ d ∈ u.drop (n + B), d = 0 := by
    intro d hd
    have e : u.drop (n + B) = (u.drop (j + n)).drop (B - j) := by rw [List.drop_drop]; congr 1; omega
    rw [e] at hd
    exact htail d (List.mem_of_mem_drop hd)
  have hultB : val u < 2 ^ (64 * (n + B)) := lt_of_drop_zero hu htail'
  -- the normalised argument
  obtain ⟨k, hk, hnk, hzk⟩ := norm_eq_take (u.drop (B - 1))
  have hnl : (norm (u.drop (B - 1))).length = k := by have hk' := hk; simp at hk'; rw [hnk]; simp; omega
  have hvarg : val (norm (u.drop (B - 1))) = val u / 2 ^ (64 * (B - 1)) := by
    rw [val_norm]; exact (val_take_mod u _ hu).2
  have hargt : val (norm (u.drop (B - 1))) < 2 ^ (64 * (n + 1)) := by
    rw [hvarg, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow64_add]
    exact Nat.lt_of_lt_of_le hultB (pow_le_pow_64 (by omega))
  have hla : k ≤ n + 1 := by
    rw [← hnl]; exact length_le_of_normed (Wd_norm (hu.drop _)) (normed_norm _) hargt
  have hkl : k ≤ (u.drop (B - 1)).length := hk
  have hdl : (u.drop (B - 1)).length = m + n - (B - 1) := by simp [hul]
  have htl : ∀ d ∈ u.drop (B - 1 + k), d = 0 := by
    intro d hd
    rw [← List.drop_drop] at hd
    exact hzk d hd
  have hXv : val u < val v * 2 ^ (64 * (B + 1)) :=
    Nat.lt_of_lt_of_le hbd (Nat.mul_le_mul_left _ (pow_le_pow_64 (by omega)))
  have hLn : n ≤ u.length := by omega
  have hcore := step_core rec N hrec mul hmul true v n (B - 1) B u k hv hvn htop hsB h2B hnN hu hLn hla (by have h1 := hkl; have h2 := hdl; have h3 := hul; omega) htl hXv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := hcore
  have hfinR : finR rec v B u = rec (List.replicate (B + 1) 0) ((u.drop (B - 1)).take k) (v.drop (B - 1)) := by
    unfold finR; rw [hnk]
  have hfinM : finM rec mul v n B u = refMid mul true v n (B - 1)
      (norm (rec (List.replicate (B + 1) 0) ((u.drop (B - 1)).take k) (v.drop (B - 1))).1)
      (upd u (B - 1) (rec (List.replicate (B + 1) 0) ((u.drop (B - 1)).take k) (v.drop (B - 1))).2) := by
    unfold finM; rw [hfinR]
  have e5 : (finM rec mul v n B u).q.length ≤ B + 1 := by rw [hfinM]; exact c5
  have e6 : Wd (finM rec mul v n B u).q := by rw [hfinM]; exact c6
  have e7 : val (finM rec mul v n B u).q = val u / val v := by rw [hfinM]; exact c7
  have e8 : (finM rec mul v n B u).w.length = u.length := by rw [hfinM]; exact c8
  have e9 : Wd (finM rec mul v n B u).w := by rw [hfinM]; exact c9
  have e10 : val (finM rec mul v n B u).w = val u % val v := by rw [hfinM]; exact c10
  have e11 : (finM rec mul v n B u).c = 0 := by rw [hfinM]; exact c11
  have e12 : (finM rec mul v n B u).e ≤ 0 := by rw [hfinM]; exact c12
  have e13 : (norm (finR rec v B u).1).length + (B - 1) ≤ 3 * n := by rw [hfinR]; exact c13
  unfold finalBlock
  simp only []
  generalize finM rec mul v n B u = M at *
  have hdm := Nat.div_add_mod (val u) (val v)
  have hnq : Wd (norm M.q) := Wd_norm e6
  have hvq : val (norm M.q) = val u / val v := by rw [val_norm, e7]
  have hnoz : val z + val u / val v < 2 ^ (64 * lz) := by
    have h1 : val v * (val u / val v) ≤ val u := Nat.mul_div_le _ _
    have h3 : val v * (val z + val u / val v) < val v * 2 ^ (64 * lz) := by rw [Nat.mul_add]; omega
    exact Nat.lt_of_mul_lt_mul_left h3
  have hqlen : (norm M.q).length ≤ lz := by
    refine length_le_of_normed hnq (normed_norm _) ?_
    rw [hvq]; omega
  obtain ⟨a1, a2, a3⟩ := addTo_spec z (norm M.q) hz hnq (by rw [hzl]; exact hqlen) (by rw [hvq, hzl]; omega)
  have hvlt' : val u % val v < 2 ^ (64 * n) := Nat.lt_of_lt_of_le (Nat.mod_lt _ hvp) (Nat.le_of_lt hvlt)
  refine ⟨by rw [a1, hzl], by rw [e8, hul], a2, e9, ?_, ?_, ?_, e11, e12, e13, hqlen⟩
  · rw [a3, hvq]
    have := (Nat.div_mod_unique hvp).2 (show val u % val v + val v * (val z + val u / val v) = U0 ∧ val u % val v < val v from
      ⟨by rw [Nat.mul_add]; omega, Nat.mod_lt _ hvp⟩)
    exact this.1.symm
  · rw [e10]
    have := (Nat.div_mod_unique hvp).2 (show val u % val v + val v * (val z + val u / val v) = U0 ∧ val u % val v < val v from
      ⟨by rw [Nat.mul_add]; omega, Nat.mod_lt _ hvp⟩)
    exact this.2.symm
  · exact zero_drop_of_lt e9 (by rw [e10]; exact hvlt')

end FvModexp.Mdl
