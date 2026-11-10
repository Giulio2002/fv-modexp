import FvModexp.Proofs.Common.DivBasicEstWin
/-!
# `divBasic` (natdiv.go:646-722): Knuth algorithm D, model and the loop invariant

```go
func (q nat) divBasic(stk *stack, u, v nat) {
    n := len(v); m := len(u) - n
    ...
    vn1 := v[n-1]; rec := reciprocalWord(vn1)
    ujn := Word(0)
    for j := m; j >= 0; j-- {
        qhat := estimate ...                       // DivBasicEst.lean (qhatEst)
        qhatv, qhl, subVV, addVV, u[j+n] += c ...  // DivBasicStep.lean (dbSubAdd)
        ujn = u[j+n-1]
        if j == m && m == len(q) && qhat == 0 { continue }
        q[j] = qhat
    }
}
```
* `dbStep`   one iteration (natdiv.go:667-720)
* `dbLoop`   the `for` loop; `dbLoop k` runs `j = k-1, ..., 0`
* `divBasic` natdiv.go:646
-/
namespace FvModexp.Mdl

/-- One loop iteration (natdiv.go:667-721): returns the new `q`, `u` and `ujn`. -/
def dbStep (v : List Nat) (vn1 rec m j : Nat) (q u : List Nat) (ujn : Nat) : List Nat × List Nat × Nat :=
  let n := v.length
  let qhat := qhatEst vn1 (v.getD (n - 2) 0) rec ujn (u.getD (j + n - 1) 0) (u.getD (j + n - 2) 0)
  let r := dbSubAdd v j qhat u
  let q' := if j = m ∧ m = q.length ∧ r.2 = 0 then q else upd q j [r.2]    -- `continue` / `q[j] = qhat`
  (q', r.1, r.1.getD (j + n - 1) 0)                                          -- ujn = u[j+n-1]

/-- `for j := m; j >= 0; j-- { ... }`, `k = j + 1` iterations left. -/
def dbLoop (v : List Nat) (vn1 rec m : Nat) : Nat → List Nat → List Nat → Nat → List Nat × List Nat
  | 0, q, u, _ => (q, u)
  | k + 1, q, u, ujn =>
    let r := dbStep v vn1 rec m k q u ujn
    dbLoop v vn1 rec m k r.1 r.2.1 r.2.2

/-- natdiv.go:646 `(q nat) divBasic(stk, u, v)`: returns the final `q` and `u` (the remainder). -/
def divBasic (q u v : List Nat) : List Nat × List Nat :=
  if u.length < v.length then (q, u)       -- m < 0: the loop does not run
  else dbLoop v (topLimb v) (reciprocalWord (topLimb v)) (u.length - v.length) (u.length - v.length + 1) q u 0

/-- Loop invariant before running iteration `j = k - 1` (so digits `≥ k` are done); `m = len u0 - len v`. -/
def DbInv (v u0 q0 : List Nat) (m k : Nat) (q u : List Nat) (ujn : Nat) : Prop :=
  Wd q ∧ Wd u ∧ q.length = q0.length ∧ u.length = u0.length ∧
  u.take k = u0.take k ∧ val (u.drop k) = val (u0.drop k) % val v ∧
  (0 < k → ujn = u.getD (k - 1 + v.length) 0) ∧
  q.take k = q0.take k ∧ q.drop (m + 1) = q0.drop (m + 1) ∧
  val ((q.drop k).take (m + 1 - k)) = val (u0.drop k) / val v

theorem getD_take_lt (L : List Nat) (i k : Nat) (h : i < k) : (L.take k).getD i 0 = L.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem drop_upd_single (q : List Nat) (d j : Nat) (h : j < q.length) : (upd q j [d]).drop j = d :: q.drop (j + 1) := by
  unfold upd
  have : (q.take j).length = j := by simp; omega
  simp [List.drop_append, this]


/-- One iteration preserves the invariant and does not panic: every slice used is in range
(`j + n ≤ len u`, `qhatv[n] == 0` whenever `j + n + 1 > len u`, and `q[j]` in range unless skipped). -/
theorem dbStep_inv (v u0 q0 : List Nat) (m j : Nat) (q u : List Nat) (ujn : Nat)
    (hv : Wd v) (hn : 2 ≤ v.length) (hb : 2 ^ 63 ≤ topLimb v) (hu0 : Wd u0) (hmd : m + v.length = u0.length)
    (hjm : j ≤ m)
    (hm : m ≤ q0.length ∧ (m = q0.length → val (u0.drop m) < val v))
    (hI : DbInv v u0 q0 m (j + 1) q u ujn) :
    DbInv v u0 q0 m j (dbStep v (topLimb v) (reciprocalWord (topLimb v)) m j q u ujn).1
      (dbStep v (topLimb v) (reciprocalWord (topLimb v)) m j q u ujn).2.1
      (dbStep v (topLimb v) (reciprocalWord (topLimb v)) m j q u ujn).2.2 ∧
    j + v.length ≤ u.length ∧
    (u.length = j + v.length →
      (mulAddVWW v (qhatEst (topLimb v) (v.getD (v.length - 2) 0) (reciprocalWord (topLimb v)) ujn
        (u.getD (j + v.length - 1) 0) (u.getD (j + v.length - 2) 0)) 0).2 = 0) ∧
    (¬ (j = m ∧ m = q.length ∧ (dbSubAdd v j (qhatEst (topLimb v) (v.getD (v.length - 2) 0) (reciprocalWord (topLimb v)) ujn
        (u.getD (j + v.length - 1) 0) (u.getD (j + v.length - 2) 0)) u).2 = 0) → j < q.length) := by
  obtain ⟨hWq, hWu, hql, hul, hut, huv, hujn, hqt, hqd, hqv⟩ := hI
  have hD0 : 0 < val v := by
    have := val_ge_top v
    have h2 : 0 < 2 ^ (64 * (v.length - 1)) := Nat.two_pow_pos _
    have : 0 < topLimb v * 2 ^ (64 * (v.length - 1)) := Nat.mul_pos (by omega) h2
    unfold topLimb at *; omega
  have hDlt : val v < 2 ^ (64 * v.length) := val_lt hv
  have hjlt : j < u.length := by omega
  -- the window
  have F1 : u.getD j 0 = u0.getD j 0 := by
    rw [← getD_take_lt u j (j + 1) (by omega), hut, getD_take_lt _ _ _ (by omega)]
  have hY' : val (u.drop (j + 1)) = val (u0.drop (j + 1)) % val v := huv
  have hmodlt : val (u0.drop (j + 1)) % val v < val v := Nat.mod_lt _ hD0
  have hX : val (u.drop j) = u0.getD j 0 + 2 ^ 64 * (val (u0.drop (j + 1)) % val v) := by
    rw [val_drop_cons u j, F1, hY']
  have hXD : val (u.drop j) < 2 ^ 64 * val v := by
    have h1 : u0.getD j 0 < 2 ^ 64 := wd_getD hu0 _
    have h2 : 2 ^ 64 * (val (u0.drop (j + 1)) % val v + 1) ≤ 2 ^ 64 * val v := Nat.mul_le_mul_left _ hmodlt
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  have hzero : val (u.drop (j + v.length + 1)) = 0 := by
    have h1 : val (u.drop (j + 1)) < 2 ^ (64 * v.length) := by rw [hY']; omega
    have := val_drop_zero (u.drop (j + 1)) v.length h1 (hWu.drop _)
    rw [List.drop_drop] at this
    have e : j + 1 + v.length = j + v.length + 1 := by omega
    rwa [e] at this
  have hujn' : ujn = u.getD (j + v.length) 0 := by
    have := hujn (by omega)
    rw [this]; congr 1
  obtain ⟨e1, e2, e3, e4⟩ := est_facts v u j ujn hv hWu hn hb (by omega) hzero hXD hujn' _ rfl
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := dbSubAdd_spec v u j _ hv hWu e3 hn (by omega) hD0 hzero ⟨e1, e2⟩ hXD e4
  -- arithmetic on the running quotient / remainder
  obtain ⟨hy1, hy2⟩ := Y_arith (u0.getD j 0) (val (u0.drop (j + 1))) (val v) (val (u.drop j)) hD0 hX
  have hY0 : val (u0.drop j) = u0.getD j 0 + 2 ^ 64 * val (u0.drop (j + 1)) := val_drop_cons u0 j
  rw [← hY0] at hy1 hy2
  have hqB : val (u.drop j) / val v < 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hXD
  unfold dbStep
  dsimp only
  generalize qhatEst (topLimb v) (v.getD (v.length - 2) 0) (reciprocalWord (topLimb v)) ujn
    (u.getD (j + v.length - 1) 0) (u.getD (j + v.length - 2) 0) = qhat at *
  generalize dbSubAdd v j qhat u = r at *
  obtain ⟨r1, r2⟩ := r
  dsimp only at s1 s2 s3 s4 s5 ⊢
  have hz0 : j = m → m = q.length → r2 = 0 := by
    intro h1 h2
    subst h1
    have : val (u0.drop j) / val v = 0 := Nat.div_eq_of_lt (hm.2 (by omega))
    omega
  have hstore : ¬ (j = m ∧ m = q.length ∧ r2 = 0) → j < q.length := by
    intro h
    refine Nat.lt_of_not_le (fun hle => h ⟨by omega, by omega, hz0 (by omega) (by omega)⟩)
  have htq : q.take j = q0.take j := by
    have := congrArg (List.take j) hqt
    simpa [List.take_take, Nat.min_eq_left (Nat.le_succ j)] using this
  have htu : r1.take j = u0.take j := by
    have := congrArg (List.take j) hut
    rw [s3]
    simpa [List.take_take, Nat.min_eq_left (Nat.le_succ j)] using this
  have hqall : Wd (if j = m ∧ m = q.length ∧ r2 = 0 then q else upd q j [r2]) ∧
      (if j = m ∧ m = q.length ∧ r2 = 0 then q else upd q j [r2]).length = q0.length ∧
      (if j = m ∧ m = q.length ∧ r2 = 0 then q else upd q j [r2]).take j = q0.take j ∧
      (if j = m ∧ m = q.length ∧ r2 = 0 then q else upd q j [r2]).drop (m + 1) = q0.drop (m + 1) ∧
      val (((if j = m ∧ m = q.length ∧ r2 = 0 then q else upd q j [r2]).drop j).take (m + 1 - j)) =
        val (u0.drop j) / val v := by
    by_cases hsk : j = m ∧ m = q.length ∧ r2 = 0
    · rw [if_pos hsk]
      obtain ⟨h1, h2, h3⟩ := hsk
      have hdrop : q.drop j = [] := List.drop_eq_nil_of_le (by omega)
      have : val (u0.drop j) / val v = 0 := by
        have := hm.2 (by omega); rw [← h1] at this; exact Nat.div_eq_of_lt this
      refine ⟨hWq, hql, htq, hqd, ?_⟩
      rw [hdrop]; simpa using this.symm
    · rw [if_neg hsk]
      have hj := hstore hsk
      have hr2 : r2 < 2 ^ 64 := by omega
      refine ⟨Wd_upd hWq (by intro d hd; simp at hd; subst hd; exact hr2), ?_, ?_, ?_, ?_⟩
      · rw [length_upd _ _ _ (by simp; omega)]; exact hql
      · rw [take_upd_near _ _ _ (by simp; omega)]; exact htq
      · rw [drop_upd_far _ _ _ _ (by simp; omega) (by simp; omega)]; exact hqd
      · rw [drop_upd_single _ _ _ hj]
        have e : m + 1 - j = (m - j) + 1 := by omega
        rw [e, List.take_succ_cons, val_cons]
        have hqv' : m + 1 - (j + 1) = m - j := by omega
        rw [hqv'] at hqv
        rw [hqv, hy2, s5]
  obtain ⟨c1, c2, c3, c4, c5⟩ := hqall
  have hex : ¬ (j = m ∧ m = q.length ∧ r2 = 0) → j < q.length := hstore
  refine ⟨⟨c1, s2, c2, by omega, htu, by rw [s4, hy1], ?_, c3, c4, c5⟩, by omega, s6, ?_⟩
  · intro hj
    congr 1; omega
  · exact hex


theorem dbLoop_inv (v u0 q0 : List Nat) (m : Nat)
    (hv : Wd v) (hn : 2 ≤ v.length) (hb : 2 ^ 63 ≤ topLimb v) (hu0 : Wd u0) (hmd : m + v.length = u0.length)
    (hm : m ≤ q0.length ∧ (m = q0.length → val (u0.drop m) < val v)) :
    ∀ (k : Nat) (q u : List Nat) (ujn : Nat), k ≤ m + 1 → DbInv v u0 q0 m k q u ujn →
      ∃ ujn', DbInv v u0 q0 m 0 (dbLoop v (topLimb v) (reciprocalWord (topLimb v)) m k q u ujn).1
        (dbLoop v (topLimb v) (reciprocalWord (topLimb v)) m k q u ujn).2 ujn'
  | 0, q, u, ujn, _, hI => ⟨ujn, by unfold dbLoop; exact hI⟩
  | k + 1, q, u, ujn, hk, hI => by
    obtain ⟨h1, _⟩ := dbStep_inv v u0 q0 m k q u ujn hv hn hb hu0 hmd (by omega) hm hI
    unfold dbLoop
    exact dbLoop_inv v u0 q0 m hv hn hb hu0 hmd hm k _ _ _ (by omega) h1

/-- `divBasic` satisfies the interface contract used by `divLarge` / `divRecursiveStep` (DivContract.lean). -/
theorem divBasic_contract : DivBasicContract divBasic := by
  intro q u v hq hu hv hn htop
  refine ⟨fun h => by simp [divBasic, h], fun hle hcase => ?_⟩
  have hD0 : 0 < val v := by
    have := val_ge_top v
    have h2 : 0 < 2 ^ (64 * (v.length - 1)) := Nat.two_pow_pos _
    have : 0 < topLimb v * 2 ^ (64 * (v.length - 1)) := Nat.mul_pos (by omega) h2
    unfold topLimb at *; omega
  have hDlt : val v < 2 ^ (64 * v.length) := val_lt hv
  have hDge : 2 ^ (64 * (v.length - 1)) ≤ val v := by
    have := val_ge_top v
    have h2 : 2 ^ (64 * (v.length - 1)) ≤ topLimb v * 2 ^ (64 * (v.length - 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    unfold topLimb at *; omega
  obtain ⟨m, hmd⟩ : ∃ m, m + v.length = u.length := ⟨u.length - v.length, by omega⟩
  have hmm : u.length - v.length = m := by omega
  have hm : m ≤ q.length ∧ (m = q.length → val (u.drop m) < val v) := by
    rcases hcase with h | ⟨h1, h2⟩
    · exact ⟨by omega, fun h' => by omega⟩
    · refine ⟨by omega, fun _ => ?_⟩
      have hs := val_split u m (by omega)
      have hm' : q.length = m := by omega
      rw [hm'] at h2
      refine Nat.lt_of_not_le (fun hge => ?_)
      have := Nat.mul_le_mul_left (2 ^ (64 * m)) hge
      rw [Nat.mul_comm (val v)] at h2
      omega
  -- initial invariant
  have hlen1 : (u.drop (m + 1)).length = v.length - 1 := by simp; omega
  have hlt1 : val (u.drop (m + 1)) < val v := by
    have := val_lt (hu.drop (m + 1))
    rw [hlen1] at this; omega
  have hI0 : DbInv v u q m (m + 1) q u 0 := by
    refine ⟨hq, hu, rfl, rfl, rfl, ?_, fun _ => ?_, rfl, rfl, ?_⟩
    · exact (Nat.mod_eq_of_lt hlt1).symm
    · simp only [Nat.add_sub_cancel]
      exact (getD_out u _ (by omega)).symm
    · simp only [Nat.sub_self, List.take_zero, val_nil]
      exact (Nat.div_eq_of_lt hlt1).symm
  obtain ⟨ujn', hI⟩ := dbLoop_inv v u q m hv hn htop hu hmd hm (m + 1) q u 0 (Nat.le_refl _) hI0
  have hdb : divBasic q u v = dbLoop v (topLimb v) (reciprocalWord (topLimb v)) m (m + 1) q u 0 := by
    unfold divBasic; rw [if_neg (by omega), hmm]
  rw [hdb]
  rw [hdb] at *
  generalize dbLoop v (topLimb v) (reciprocalWord (topLimb v)) m (m + 1) q u 0 = r at *
  obtain ⟨r1, r2⟩ := r
  obtain ⟨i1, i2, i3, i4, _, i6, _, _, i8, i9⟩ := hI
  dsimp only at *
  have e1 : u.length - v.length + 1 = m + 1 := by omega
  rw [e1]
  have hr2 : val r2 = val u % val v := by simpa using i6
  refine ⟨i3, i4, i1, i2, ?_, i8, hr2, ?_⟩
  · simpa using i9
  · intro d hd
    have hmod : val u % val v < 2 ^ (64 * v.length) := by
      have := Nat.mod_lt (val u) hD0; omega
    have := val_drop_zero r2 v.length (by rw [hr2]; exact hmod) i2
    exact val_eq_zero_iff.1 this d hd

end FvModexp.Mdl
