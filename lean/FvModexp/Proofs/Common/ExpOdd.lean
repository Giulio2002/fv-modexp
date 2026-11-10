import FvModexp.Proofs.Common.ExpWindow
import FvModexp.Proofs.Common.ExpMont
/-
  ExpOdd: expNNOdd / expNNOddMontgomeryWindowSize{2,4}  (nat.go:1343-1360, 1363-1494, 1496-1700)
  and their correctness  `x^y mod m` for odd m.
-/
namespace FvModexp.Exp

/-! ### small modular-arithmetic lemmas (core Lean has no `Nat.ModEq`) -/

theorem cg_of_dvd_sub {m a b : Nat} (hab : b ≤ a) (h : m ∣ a - b) : a % m = b % m := by
  obtain ⟨q, hq⟩ := h
  have : a = b + m * q := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem cg_cancel {m R a b : Nat} (hco : Nat.Coprime R m) (h : a * R % m = b * R % m) :
    a % m = b % m := by
  rcases Nat.le_total b a with hba | hab
  · have h1 : (a * R - b * R) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [← Nat.sub_mul] at h1
    have h2 : m ∣ (a - b) * R := Nat.dvd_of_mod_eq_zero h1
    have h3 : m ∣ a - b := (Nat.Coprime.symm hco).dvd_of_dvd_mul_right h2
    exact cg_of_dvd_sub hba h3
  · have h1 : (b * R - a * R) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [← Nat.sub_mul] at h1
    have h2 : m ∣ (b - a) * R := Nat.dvd_of_mod_eq_zero h1
    have h3 : m ∣ b - a := (Nat.Coprime.symm hco).dvd_of_dvd_mul_right h2
    exact (cg_of_dvd_sub hab h3).symm

theorem coprime_B_pow_odd (n m : Nat) (hm : m % 2 = 1) : Nat.Coprime (B ^ n) m := by
  rw [B_def, ← Nat.pow_mul]
  refine Nat.Coprime.pow_left _ ?_
  show Nat.gcd 2 m = 1
  rw [Nat.gcd_rec, hm]; rfl

/-- One `nat.montgomery` call is an exact Montgomery product (output stays `< B^n`). -/
theorem mont_rep (n m k a b : Nat) (hn : 1 ≤ n) (ha : a < B ^ n) (hb : b < B ^ n) (hm : m < B ^ n)
    (hk : (k * m + 1) % B = 0) :
    montgomery n a b m k < B ^ n ∧ montgomery n a b m k * B ^ n % m = a * b % m := by
  obtain ⟨Q, T, hQ, hT, hTlt, hr⟩ := montgomery_spec n a b m k hn ha hb hm hk
  have hTm : T * B ^ n % m = a * b % m := by
    rw [hT, Nat.add_mul_mod_self_right]
  rw [hr]
  split
  · rename_i hRT
    have hmT : m ≤ T := by omega
    refine ⟨by omega, ?_⟩
    have : (T - m) * B ^ n + m * B ^ n = T * B ^ n := by
      rw [← Nat.add_mul]; congr 1; omega
    rw [← hTm, ← this, Nat.add_mul_mod_self_left]
  · rename_i hRT
    exact ⟨by omega, hTm⟩

/-- `Rep z e`: `z` is the Montgomery form (`·B^n`) of `x^e` modulo `m`. -/
def MRep (n m x z e : Nat) : Prop := z < B ^ n ∧ z % m = x ^ e * B ^ n % m

section oddexp
variable (n m k x : Nat)

theorem mont_mul_rep (hn : 1 ≤ n) (hm : m < B ^ n) (hmo : m % 2 = 1) (hk : (k * m + 1) % B = 0)
    {z z' e e' : Nat} (h : MRep n m x z e) (h' : MRep n m x z' e') :
    MRep n m x (montgomery n z z' m k) (e + e') := by
  obtain ⟨hr1, hr2⟩ := mont_rep n m k z z' hn h.1 h'.1 hm hk
  refine ⟨hr1, ?_⟩
  apply cg_cancel (R := B ^ n) (coprime_B_pow_odd n m hmo)
  rw [hr2, Nat.mul_mod, h.2, h'.2, ← Nat.mul_mod]
  congr 1; rw [Nat.pow_add]; grind

theorem msq_iter_rep (hn : 1 ≤ n) (hm : m < B ^ n) (hmo : m % 2 = 1) (hk : (k * m + 1) % B = 0) :
    ∀ (j z e : Nat), MRep n m x z e →
      MRep n m x (iter (fun z => montgomery n z z m k) j z) (e * 2 ^ j) := by
  intro j
  induction j with
  | zero => intro z e h; simpa [iter] using h
  | succ j ih =>
    intro z e h
    have := ih _ _ (mont_mul_rep n m k x hn hm hmo hk h h)
    simp only [iter]
    have e2 : (e + e) * 2 ^ j = e * 2 ^ (j + 1) := by rw [Nat.pow_succ]; grind
    rw [e2] at this
    exact this

end oddexp

/-! ### The Go routines -/

/-- `powers[0..2^w)` (nat.go:1409-1417): `powers[0]=mont(one,RR)`, `powers[1]=mont(x,RR)`,
`powers[i]=mont(powers[i-1], powers[1])`. -/
def montPow (n m k x1 RR : Nat) : Nat → Nat
  | 0 => montgomery n 1 RR m k
  | 1 => montgomery n x1 RR m k
  | i + 2 => montgomery n (montPow n m k x1 RR (i + 1)) (montgomery n x1 RR m k) m k

/-- `expNNOddMontgomeryWindowSize{2,4}` (nat.go:1363-1494 / 1496-1700), window size `w` ∈ {2,4}.
Memory-management moves (z/zz buffer swaps, stk) are not modelled; they do not change values. -/
def expNNOddMont (w : Nat) (x y m : Nat) : Nat :=
  let n := nlen m                                  -- numWords := len(m)
  let x1 := if n < nlen x then x % m else x        -- if len(x) > numWords { x = x mod m }
  if y = 0 then 1                                  -- if len(y) == 0 { return 1 }
  else
    let k := montK0 (m % B)                        -- k0 := computeMontgomeryk0(m[0])
    let RR := B ^ (2 * n) % m                      -- RR = 2^(2*_W*len(m)) mod m
    let tbl := montPow n m k x1 RR
    let step := fun z d => montgomery n (iter (fun z => montgomery n z z m k) w z) (tbl d) m k
    let i := nlen y - 1
    let z := winRun w step tbl y i (wd y i)
    let zz := montgomery n z 1 m k                 -- convert to regular number
    if m ≤ zz then                                 -- zz.cmp(m) >= 0
      let zz1 := zz - m
      if m ≤ zz1 then zz1 % m else zz1             -- (never reached) div fallback
    else zz

/-- `expNNOdd` (nat.go:1343): 4-bit window iff `len(y) > 64/_W`. -/
def expNNOdd (x y m : Nat) : Nat :=
  if nlen y > 1 then expNNOddMont 4 x y m else expNNOddMont 2 x y m

theorem nlen_pos {x : Nat} (hx : 0 < x) : 1 ≤ nlen x := by
  unfold nlen; simp only [Nat.ne_of_gt hx, ite_false]; omega

theorem nlen_minimal {y : Nat} (hy : 0 < y) : B ^ (nlen y - 1) ≤ y := by
  refine Nat.not_lt.mp (fun h => ?_)
  have := nlen_le_iff.mpr h
  have := nlen_pos hy
  omega

theorem montK0_hk (m : Nat) (hm : m % 2 = 1) : (montK0 (m % B) * m + 1) % B = 0 := by
  have h := montK0_spec (m % B) (by
    have : m % B % 2 = m % 2 := by
      rw [B_def]; exact Nat.mod_mod_of_dvd _ (by exact ⟨2 ^ 63, by decide⟩)
    omega) (Nat.mod_lt _ B_pos)
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at h
  rw [Nat.add_mod, Nat.mul_mod]
  exact h

theorem expNNOddMont_correct (w : Nat) (hw : w = 2 ∨ w = 4) (x y m : Nat) (hm : m % 2 = 1)
    (hy : 0 < y) : expNNOddMont w x y m = x ^ y % m := by
  have hw0 : 0 < w := by omega
  have hK : 64 / w * w = 64 := by rcases hw with rfl | rfl <;> decide
  have hw64 : w ≤ 64 := by omega
  have hm0 : 0 < m := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = nlen m := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := hn ▸ nlen_pos hm0
  have hmB : m < B ^ n := hn ▸ lt_B_nlen m
  have hk := montK0_hk m hm
  obtain ⟨k, hkd⟩ : ∃ k, k = montK0 (m % B) := ⟨_, rfl⟩
  rw [← hkd] at hk
  obtain ⟨x1, hx1d⟩ : ∃ x1, x1 = (if n < nlen x then x % m else x) := ⟨_, rfl⟩
  have hx1B : x1 < B ^ n := by
    rw [hx1d]; split
    · exact Nat.lt_trans (Nat.mod_lt _ hm0) hmB
    · rename_i h; exact nlen_le_iff.mp (by omega)
  have hx1m : x1 % m = x % m := by
    rw [hx1d]; split
    · exact Nat.mod_mod _ _
    · rfl
  obtain ⟨RR, hRRd⟩ : ∃ RR, RR = B ^ (2 * n) % m := ⟨_, rfl⟩
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
  -- top word of y
  have hyn := nlen_pos hy
  obtain ⟨i, hi⟩ : ∃ i, i = nlen y - 1 := ⟨_, rfl⟩
  have hyB : y < B ^ (i + 1) := by
    have := lt_B_nlen y
    rwa [show nlen y = i + 1 by omega] at this
  have hyge : B ^ i ≤ y := hi ▸ nlen_minimal hy
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
  unfold expNNOddMont
  simp only
  rw [← hn, ← hkd, ← hx1d, ← hRRd, if_neg (by omega), ← hi]
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
  by_cases hmz : m ≤ zz
  · rw [if_pos hmz]
    have hzm : zz = m := by omega
    have : ¬ m ≤ zz - m := by omega
    rw [if_neg this]
    have : zz % m = 0 := by rw [hzm]; exact Nat.mod_self m
    omega
  · rw [if_neg hmz, ← hzzm, Nat.mod_eq_of_lt (by omega)]

theorem expNNOdd_correct (x y m : Nat) (hm : m % 2 = 1) (hy : 0 < y) :
    expNNOdd x y m = x ^ y % m := by
  unfold expNNOdd
  split
  · exact expNNOddMont_correct 4 (Or.inr rfl) x y m hm hy
  · exact expNNOddMont_correct 2 (Or.inl rfl) x y m hm hy

end FvModexp.Exp
