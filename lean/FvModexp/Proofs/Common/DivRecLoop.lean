import FvModexp.Proofs.Common.DivRecCore
/-!
# The wide-digit loop of `divRecursiveStep` (natdiv.go:777-838) and the final block (natdiv.go:845-892)

* `blockStep`: one iteration of `for j > B { ... }` (natdiv.go:778-838), on the in-place dividend `u` and the quotient `z`.
* `drsLoop`: the loop `j := m; for j > B { ...; j -= B }` (fuel = `j`, each iteration decreases `j` by `B >= 1`).
* `finalBlock`: natdiv.go:845-892 (the last, partial wide digit).
-/
namespace FvModexp.Mdl

/-- The recursive call of a loop iteration: `qhat.divRecursiveStep(stk, uu[s:B+n], v[s:], depth+1)` on a cleared `qhat` of length
`B+1` (natdiv.go:790-796); returns the final contents of `qhat` and of `uu[s:B+n]`. -/
def blockR (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (v : List Nat) (n B j : Nat) (u : List Nat) :
    List Nat × List Nat :=
  rec (List.replicate (B + 1) 0) (sl (u.drop (j - B)) (B - 1) (B + n - (B - 1))) (v.drop (B - 1))

/-- The refinement of one iteration (natdiv.go:797-834): `uu := u[j-B:]` with `uu[s:B+n] := r̂`. -/
def blockM (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (v : List Nat) (n B j : Nat) (u : List Nat) : RM :=
  refMid mul false v n (B - 1) (norm (blockR rec v n B j u).1) (upd (u.drop (j - B)) (B - 1) (blockR rec v n B j u).2)

/-- One loop iteration (natdiv.go:778-837); `addTo(z[j-B:], qhat)` (natdiv.go:835) and the in-place update of `uu = u[j-B:]`. -/
def blockStep (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (v : List Nat) (n B j : Nat) (z u : List Nat) : List Nat × List Nat :=
  (upd z (j - B) (addTo (z.drop (j - B)) (blockM rec mul v n B j u).q), upd u (j - B) (blockM rec mul v n B j u).w)

/-- `for j > B { ...; j -= B }` (natdiv.go:777-838). Fuel `f >= j` suffices. -/
def drsLoop (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (v : List Nat) (n B : Nat) : Nat → Nat → List Nat → List Nat → List Nat × List Nat
  | 0, _, z, u => (z, u)
  | f + 1, j, z, u =>
    if B < j then
      let r := blockStep rec mul v n B j z u
      drsLoop rec mul v n B f (j - B) r.1 r.2
    else (z, u)

/-- The recursive call of the final block: `qhat.divRecursiveStep(stk, u[s:].norm(), v[s:], depth+1)` (natdiv.go:853). -/
def finR (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (v : List Nat) (B : Nat) (u : List Nat) :
    List Nat × List Nat :=
  rec (List.replicate (B + 1) 0) (norm (u.drop (B - 1))) (v.drop (B - 1))

/-- The refinement of the final block (natdiv.go:854-889). -/
def finM (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (v : List Nat) (n B : Nat) (u : List Nat) : RM :=
  refMid mul true v n (B - 1) (norm (finR rec v B u).1) (upd u (B - 1) (finR rec v B u).2)

/-- The final block: returns `(z', u')` (`addTo(z, qhat.norm())`, natdiv.go:892). -/
def finalBlock (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (v : List Nat) (n B : Nat) (z u : List Nat) : List Nat × List Nat :=
  (addTo z (norm (finM rec mul v n B u).q), (finM rec mul v n B u).w)

/-! ### one iteration -/

theorem pow_le_pow_64 {a b : Nat} (h : a ≤ b) : 2 ^ (64 * a) ≤ 2 ^ (64 * b) := Nat.pow_le_pow_right (by decide) (by omega)

theorem pow64_add (a b : Nat) : 2 ^ (64 * (a + b)) = 2 ^ (64 * a) * 2 ^ (64 * b) := by
  rw [Nat.mul_add, Nat.pow_add]

theorem blockStep_spec (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (N : Nat) (hrec : RecOk rec N)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul)
    (v : List Nat) (n B j m lz U0 : Nat) (z u : List Nat)
    (hv : Wd v) (hvn : v.length = n) (htop : 2 ^ 63 ≤ topLimb v) (hB1 : 1 ≤ B) (h2B : 2 * B ≤ n) (hnN : n - (B - 1) ≤ N)
    (hz : Wd z) (hu : Wd u) (hzl : z.length = lz) (hul : u.length = m + n)
    (hval : val u + val v * val z = U0) (hbd : val u < val v * 2 ^ (64 * (j + 1)))
    (htail : ∀ d ∈ u.drop (j + n), d = 0) (hj : j = m ∨ j + B ≤ m) (hjB : B < j)
    (hlz : m ≤ lz) (hU0 : U0 < val v * 2 ^ (64 * lz)) (hH : 2 * U0 < 2 ^ (64 * (n + lz))) :
    (blockStep rec mul v n B j z u).1.length = lz ∧ (blockStep rec mul v n B j z u).2.length = m + n ∧
    Wd (blockStep rec mul v n B j z u).1 ∧ Wd (blockStep rec mul v n B j z u).2 ∧
    val (blockStep rec mul v n B j z u).2 + val v * val (blockStep rec mul v n B j z u).1 = U0 ∧
    val (blockStep rec mul v n B j z u).2 < val v * 2 ^ (64 * (j - B)) ∧
    (blockM rec mul v n B j u).c = 0 ∧ (blockM rec mul v n B j u).e ≤ 0 ∧
    (norm (blockR rec v n B j u).1).length + (B - 1) ≤ 3 * n ∧
    (blockM rec mul v n B j u).q.length ≤ lz - (j - B) := by
  have hjm : j ≤ m := by omega
  have hi : j - B ≤ u.length := by omega
  have hwl : (u.drop (j - B)).length = m + n - (j - B) := by simp [hul]
  have hvp : 0 < val v := by
    have := (Ctx.v1S_ge (v := v) (n := n) (s := B - 1) (B := B) (ql := 0) (L := n) ⟨hv, hvn, htop, by omega, h2B, by omega, Nat.le_refl _⟩)
    have : 0 < 2 ^ 63 * 2 ^ (64 * (n - 1)) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    have hv0 := (Ctx.v_split (v := v) (n := n) (s := B - 1) (B := B) (ql := 0) (L := n) ⟨hv, hvn, htop, by omega, h2B, by omega, Nat.le_refl _⟩)
    omega
  have hvlt : val v < 2 ^ (64 * n) := by have := val_lt hv; rwa [hvn] at this
  -- the working slice
  have hsplit := take_len_drop_val u (j - B) hi
  have hlow : val (u.take (j - B)) < 2 ^ (64 * (j - B)) := by
    have := val_lt (hu.take (j - B)); rwa [show (u.take (j - B)).length = j - B by simp; omega] at this
  have hXv : val (u.drop (j - B)) < val v * 2 ^ (64 * (B + 1)) := by
    have e : 2 ^ (64 * (j + 1)) = 2 ^ (64 * (j - B)) * 2 ^ (64 * (B + 1)) := by
      rw [← pow64_add]; congr 2; omega
    rw [e, Nat.mul_comm (2 ^ (64 * (j - B))) _ , ← Nat.mul_assoc] at hbd
    have : 2 ^ (64 * (j - B)) * val (u.drop (j - B)) ≤ val u := by omega
    have h2 : val (u.drop (j - B)) * 2 ^ (64 * (j - B)) < val v * 2 ^ (64 * (B + 1)) * 2 ^ (64 * (j - B)) := by
      rw [Nat.mul_comm (val (u.drop (j - B)))]; omega
    exact Nat.lt_of_mul_lt_mul_right h2
  have htl : ∀ d ∈ (u.drop (j - B)).drop (B - 1 + (B + n - (B - 1))), d = 0 := by
    intro d hd
    rw [List.drop_drop] at hd
    exact htail d (by rwa [show j - B + (B - 1 + (B + n - (B - 1))) = j + n by omega] at hd)
  have hcore := step_core rec N hrec mul hmul false v n (B - 1) B (u.drop (j - B)) (B + n - (B - 1)) hv hvn htop (by omega) h2B hnN
    (hu.drop _) (by omega) (by omega) (by omega) htl hXv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := hcore
  have e5 : (blockM rec mul v n B j u).q.length ≤ B + 1 := c5
  have e6 : Wd (blockM rec mul v n B j u).q := c6
  have e7 : val (blockM rec mul v n B j u).q = val (u.drop (j - B)) / val v := c7
  have e8 : (blockM rec mul v n B j u).w.length = (u.drop (j - B)).length := c8
  have e9 : Wd (blockM rec mul v n B j u).w := c9
  have e10 : val (blockM rec mul v n B j u).w = val (u.drop (j - B)) % val v := c10
  have e11 : (blockM rec mul v n B j u).c = 0 := c11
  have e12 : (blockM rec mul v n B j u).e ≤ 0 := c12
  have e13 : (norm (blockR rec v n B j u).1).length + (B - 1) ≤ 3 * n := c13
  have e14 : 2 * val (u.drop (j - B)) < 2 ^ (64 * (B + n)) → (blockM rec mul v n B j u).q.length ≤ B := c14
  unfold blockStep
  simp only []
  generalize blockM rec mul v n B j u = M at *
  generalize hwd : u.drop (j - B) = w at *
  generalize hD : val w / val v = D at *
  have hwm := Nat.div_add_mod (val w) (val v)
  rw [hD] at hwm
  -- val u = low + β^i * val w
  have hsplit' : val u = val (u.take (j - B)) + 2 ^ (64 * (j - B)) * val w := hsplit
  -- quotient digit fits
  have hfit : M.q.length ≤ lz - (j - B) := by
    rcases hj with hj | hj
    · by_cases hlt : m < lz
      · omega
      · have hlz' : lz = m := by omega
        have : M.q.length ≤ B := by
          apply e14
          have e : 2 ^ (64 * (n + lz)) = 2 ^ (64 * (B + n)) * 2 ^ (64 * (j - B)) := by
            rw [← pow64_add]; congr 2; omega
          rw [e] at hH
          have h3 : 2 ^ (64 * (j - B)) * val w ≤ U0 := by omega
          have h4 : 2 * val w * 2 ^ (64 * (j - B)) < 2 ^ (64 * (B + n)) * 2 ^ (64 * (j - B)) := by
            rw [Nat.mul_assoc, Nat.mul_comm (val w)]; omega
          exact Nat.lt_of_mul_lt_mul_right h4
        omega
    · omega
  have hzd : (z.drop (j - B)).length = lz - (j - B) := by simp [hzl]
  have hzs := take_len_drop_val z (j - B) (by omega)
  have hnoz : val z + 2 ^ (64 * (j - B)) * D < 2 ^ (64 * lz) := by
    have h1 : val v * D ≤ val w := by omega
    have h2 : val v * (2 ^ (64 * (j - B)) * D) ≤ 2 ^ (64 * (j - B)) * val w := by
      rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ h1
    have h3 : val v * (val z + 2 ^ (64 * (j - B)) * D) < val v * 2 ^ (64 * lz) := by
      rw [Nat.mul_add]; omega
    exact Nat.lt_of_mul_lt_mul_left h3
  have hno : val (z.drop (j - B)) + val M.q < 2 ^ (64 * (z.drop (j - B)).length) := by
    rw [e7, hzd]
    have e : 2 ^ (64 * lz) = 2 ^ (64 * (j - B)) * 2 ^ (64 * (lz - (j - B))) := by
      rw [← pow64_add]; congr 2; omega
    rw [e] at hnoz
    have : 2 ^ (64 * (j - B)) * (val (z.drop (j - B)) + D) < 2 ^ (64 * (j - B)) * 2 ^ (64 * (lz - (j - B))) := by
      rw [Nat.mul_add]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨a1, a2, a3⟩ := addTo_spec (z.drop (j - B)) M.q (hz.drop _) e6 (by omega) hno
  have hzu : (addTo (z.drop (j - B)) M.q).length = lz - (j - B) := by rw [a1, hzd]
  have hz'l := length_upd_full z (addTo (z.drop (j - B)) M.q) (j - B) (by omega) (by rw [hzu, hzl])
  have hz'v := val_upd_full z (addTo (z.drop (j - B)) M.q) (j - B) (by omega) (by rw [hzu, hzl])
  have hu'l := length_upd_full u M.w (j - B) hi (by rw [e8, hwl, hul])
  have hu'v := val_upd_full u M.w (j - B) hi (by rw [e8, hwl, hul])
  have hlowl : val (u.take (j - B)) < 2 ^ (64 * (j - B)) := hlow
  refine ⟨?_, ?_, Wd_upd hz a2, Wd_upd hu e9, ?_, ?_, e11, e12, e13, hfit⟩
  · exact hz'l.trans hzl
  · exact hu'l.trans hul
  · show val (upd u (j - B) M.w) + val v * val (upd z (j - B) (addTo (z.drop (j - B)) M.q)) = U0
    rw [hu'v, hz'v, a3, e7, e10, Nat.mul_add (val v)]
    have h5 : val v * (2 ^ (64 * (j - B)) * (val (z.drop (j - B)) + D)) =
        val v * (2 ^ (64 * (j - B)) * val (z.drop (j - B))) + 2 ^ (64 * (j - B)) * (val v * D) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm (val v) (2 ^ (64 * (j - B))) D]
    have h6 : val v * val z = val v * val (z.take (j - B)) + val v * (2 ^ (64 * (j - B)) * val (z.drop (j - B))) := by
      rw [hzs, Nat.mul_add]
    have h7 : 2 ^ (64 * (j - B)) * val w = 2 ^ (64 * (j - B)) * (val v * D) + 2 ^ (64 * (j - B)) * (val w % val v) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  · show val (upd u (j - B) M.w) < val v * 2 ^ (64 * (j - B))
    rw [hu'v, e10, Nat.mul_comm (val v)]
    have h8 : 2 ^ (64 * (j - B)) * (val w % val v + 1) ≤ 2 ^ (64 * (j - B)) * val v :=
      Nat.mul_le_mul_left _ (Nat.mod_lt _ hvp)
    rw [Nat.mul_add, Nat.mul_one] at h8
    omega


/-! ### the loop -/

/-- Loop invariant of `for j > B` (before the iteration with index `j`). -/
def LI (v : List Nat) (n B m lz U0 j : Nat) (z u : List Nat) : Prop :=
  Wd z ∧ Wd u ∧ z.length = lz ∧ u.length = m + n ∧ val u + val v * val z = U0 ∧
  val u < val v * 2 ^ (64 * (j + 1)) ∧ (∀ d ∈ u.drop (j + n), d = 0) ∧ (j = m ∨ j + B ≤ m)

/-- The panic-freedom facts of every iteration of the loop (`panic("impossible")` tests, final borrow). -/
def loopOk (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (mul : List Nat → List Nat → List Nat)
    (v : List Nat) (n B : Nat) : Nat → Nat → List Nat → List Nat → Prop
  | 0, _, _, _ => True
  | f + 1, j, z, u =>
    if B < j then
      (blockM rec mul v n B j u).c = 0 ∧ (blockM rec mul v n B j u).e ≤ 0 ∧
      loopOk rec mul v n B f (j - B) (blockStep rec mul v n B j z u).1 (blockStep rec mul v n B j z u).2
    else True

theorem drsLoop_spec (rec : List Nat → List Nat → List Nat → List Nat × List Nat) (N : Nat) (hrec : RecOk rec N)
    (mul : List Nat → List Nat → List Nat) (hmul : MulContract mul)
    (v : List Nat) (n B m lz U0 : Nat)
    (hv : Wd v) (hvn : v.length = n) (htop : 2 ^ 63 ≤ topLimb v) (hB1 : 1 ≤ B) (h2B : 2 * B ≤ n) (hnN : n - (B - 1) ≤ N)
    (hlz : m ≤ lz) (hU0 : U0 < val v * 2 ^ (64 * lz)) (hH : 2 * U0 < 2 ^ (64 * (n + lz))) :
    ∀ (f j : Nat) (z u : List Nat), LI v n B m lz U0 j z u → j ≤ f →
      (∃ j', j' ≤ B ∧ LI v n B m lz U0 j' (drsLoop rec mul v n B f j z u).1 (drsLoop rec mul v n B f j z u).2) ∧
      loopOk rec mul v n B f j z u
  | 0, j, z, u, hI, hj => by
    refine ⟨⟨j, by omega, hI⟩, trivial⟩
  | f + 1, j, z, u, hI, hj => by
    have hI' := hI
    obtain ⟨hz, hu, hzl, hul, hval, hbd, htail, hjm⟩ := hI
    unfold drsLoop loopOk
    by_cases hB : B < j
    · rw [if_pos hB, if_pos hB]
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := blockStep_spec rec N hrec mul hmul v n B j m lz U0 z u hv hvn htop hB1 h2B hnN
        hz hu hzl hul hval hbd htail hjm hB hlz hU0 hH
      have hvlt : val v < 2 ^ (64 * n) := by have := val_lt hv; rwa [hvn] at this
      have hnew : LI v n B m lz U0 (j - B) (blockStep rec mul v n B j z u).1 (blockStep rec mul v n B j z u).2 := by
        refine ⟨s3, s4, s1, s2, s5, ?_, ?_, by omega⟩
        · refine Nat.lt_of_lt_of_le s6 (Nat.mul_le_mul_left _ (pow_le_pow_64 (by omega)))
        · refine zero_drop_of_lt s4 ?_
          have : val v * 2 ^ (64 * (j - B)) ≤ 2 ^ (64 * n) * 2 ^ (64 * (j - B)) := Nat.mul_le_mul_right _ (Nat.le_of_lt hvlt)
          rw [← pow64_add, Nat.add_comm] at this
          exact Nat.lt_of_lt_of_le s6 this
      obtain ⟨⟨j', hj', hL⟩, hok⟩ := drsLoop_spec rec N hrec mul hmul v n B m lz U0 hv hvn htop hB1 h2B hnN hlz hU0 hH f (j - B) _ _ hnew (by omega)
      exact ⟨⟨j', hj', hL⟩, s7, s8, hok⟩
    · rw [if_neg hB, if_neg hB]
      exact ⟨⟨j, by omega, hI'⟩, trivial⟩

end FvModexp.Mdl
