/-!
# Limb lists: the value model for Go `math/big` words (`nat` = `[]Word`, `Word = uint64`)

A Go `nat` is modelled as a `List Nat` of limbs, least significant first.  `Wd l` says every limb is a 64-bit word.
`val l` is the number represented.  Slices are modelled by `take`/`drop`; a store to a sub-slice by `upd`.
Proof-only module (no machine code), pure core Lean (no Mathlib).
-/
namespace FvModexp.Mdl

/-- Numeric value of a little-endian limb list (base `2^64`). -/
def val : List Nat → Nat
  | [] => 0
  | d :: ds => d + 2 ^ 64 * val ds

/-- All limbs are 64-bit words. -/
def Wd (l : List Nat) : Prop := ∀ d ∈ l, d < 2 ^ 64

/-- Go `nat.norm`: drop the leading (most significant = trailing in the list) zero limbs. -/
def norm : List Nat → List Nat
  | [] => []
  | d :: ds => if norm ds = [] ∧ d = 0 then [] else d :: norm ds

/-- A normalised nat: no most-significant zero limb (`norm` is the identity). -/
def Normed (l : List Nat) : Prop := norm l = l

/-- Store `l` into the sub-slice of `z` starting at `i` (Go `copy(z[i:], l)` / loop stores). -/
def upd (z : List Nat) (i : Nat) (l : List Nat) : List Nat := z.take i ++ l ++ z.drop (i + l.length)

@[simp] theorem val_nil : val [] = 0 := rfl
@[simp] theorem val_cons (d : Nat) (ds : List Nat) : val (d :: ds) = d + 2 ^ 64 * val ds := rfl

theorem val_append (a b : List Nat) : val (a ++ b) = val a + 2 ^ (64 * a.length) * val b := by
  induction a with
  | nil => simp
  | cons d ds ih =>
    simp only [List.cons_append, val_cons, ih, List.length_cons]
    have : 2 ^ (64 * (ds.length + 1)) = 2 ^ 64 * 2 ^ (64 * ds.length) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    rw [this]; grind

theorem val_replicate_zero (n : Nat) : val (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem Wd_nil : Wd [] := by intro d h; simp at h
theorem Wd_cons {d : Nat} {ds : List Nat} : Wd (d :: ds) ↔ d < 2 ^ 64 ∧ Wd ds := by
  unfold Wd; simp
theorem Wd_append {a b : List Nat} : Wd (a ++ b) ↔ Wd a ∧ Wd b := by
  unfold Wd; simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun d hd => h d (Or.inl hd), fun d hd => h d (Or.inr hd)⟩
  · rintro ⟨h1, h2⟩ d (hd | hd); exact h1 d hd; exact h2 d hd
theorem Wd_replicate_zero (n : Nat) : Wd (List.replicate n 0) := by
  intro d h; have := List.eq_of_mem_replicate h; subst this; decide
theorem Wd.tail {d : Nat} {ds : List Nat} (h : Wd (d :: ds)) : Wd ds := (Wd_cons.1 h).2
theorem Wd.take {l : List Nat} (h : Wd l) (n : Nat) : Wd (l.take n) :=
  fun d hd => h d (List.mem_of_mem_take hd)
theorem Wd.drop {l : List Nat} (h : Wd l) (n : Nat) : Wd (l.drop n) :=
  fun d hd => h d (List.mem_of_mem_drop hd)

theorem val_lt {l : List Nat} (h : Wd l) : val l < 2 ^ (64 * l.length) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    have hd := (Wd_cons.1 h).1
    have := ih (Wd_cons.1 h).2
    simp only [val_cons, List.length_cons]
    have e : 2 ^ (64 * (ds.length + 1)) = 2 ^ 64 * 2 ^ (64 * ds.length) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    rw [e]
    have : 2 ^ 64 * val ds + 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * ds.length) := by
      have := Nat.mul_le_mul_left (2 ^ 64) (Nat.succ_le_of_lt this)
      rw [Nat.mul_succ] at this; exact this
    omega

theorem val_take_drop (l : List Nat) (i : Nat) :
    val l = val (l.take i) + 2 ^ (64 * (l.take i).length) * val (l.drop i) := by
  conv => lhs; rw [← List.take_append_drop i l]
  exact val_append _ _

/-- Value of a prefix / suffix split at a known position. -/
theorem val_split (l : List Nat) (i : Nat) (h : i ≤ l.length) :
    val l = val (l.take i) + 2 ^ (64 * i) * val (l.drop i) := by
  rw [val_take_drop l i]; simp [List.length_take, Nat.min_eq_left h]

theorem val_replicate_append_zero (n : Nat) (l : List Nat) :
    val (List.replicate n 0 ++ l) = 2 ^ (64 * n) * val l := by
  rw [val_append, val_replicate_zero]; simp

theorem val_append_zeros (l : List Nat) (n : Nat) : val (l ++ List.replicate n 0) = val l := by
  rw [val_append, val_replicate_zero]; simp

theorem val_eq_zero_iff {l : List Nat} : val l = 0 ↔ ∀ d ∈ l, d = 0 := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [val_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have h1 : d = 0 := by omega
      have h2 : val ds = 0 := by
        rcases Nat.eq_zero_or_pos (val ds) with h0 | hne
        · exact h0
        · have := Nat.mul_pos (Nat.two_pow_pos 64) hne; omega
      exact ⟨h1, ih.1 h2⟩
    · rintro ⟨h1, h2⟩
      have := ih.2 h2
      omega

theorem length_upd (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) : (upd z i l).length = z.length := by
  simp [upd, List.length_take, List.length_drop]; omega

theorem Wd_upd {z l : List Nat} {i : Nat} (hz : Wd z) (hl : Wd l) : Wd (upd z i l) := by
  unfold upd
  exact Wd_append.2 ⟨Wd_append.2 ⟨hz.take _, hl⟩, hz.drop _⟩

/-- Value of a store into a sub-slice: the segment is replaced. -/
theorem val_upd (z l : List Nat) (i : Nat) (h : i + l.length ≤ z.length) :
    val (upd z i l) + 2 ^ (64 * i) * val (z.drop i |>.take l.length) =
    val z + 2 ^ (64 * i) * val l := by
  unfold upd
  have h1 : (z.take i).length = i := by simp [List.length_take]; omega
  have hz : z = z.take i ++ (z.drop i).take l.length ++ z.drop (i + l.length) := by
    have e1 := List.take_append_drop l.length (z.drop i)
    have e2 : (z.drop i).drop l.length = z.drop (i + l.length) := by rw [List.drop_drop, Nat.add_comm]
    rw [e2] at e1
    rw [List.append_assoc, e1, List.take_append_drop]
  have h2 : ((z.drop i).take l.length).length = l.length := by simp [List.length_take, List.length_drop]; omega
  conv => rhs; rw [hz]
  have h3 : (z.take i ++ l).length = i + l.length := by simp [h1]
  have h4 : (z.take i ++ (z.drop i).take l.length).length = i + l.length := by simp [h1, h2]
  rw [val_append, val_append, val_append, val_append, h3, h4, h1]
  grind

/-! ### normalisation -/

@[simp] theorem norm_nil : norm [] = [] := rfl

theorem norm_cons (d : Nat) (ds : List Nat) :
    norm (d :: ds) = if norm ds = [] ∧ d = 0 then [] else d :: norm ds := rfl

theorem normed_cons {d : Nat} {ds : List Nat} : Normed (d :: ds) ↔ Normed ds ∧ ¬ (ds = [] ∧ d = 0) := by
  unfold Normed
  rw [norm_cons]
  split
  · rename_i h
    constructor
    · intro hh; exact absurd hh (by simp)
    · rintro ⟨h1, h2⟩; exfalso; apply h2
      refine ⟨?_, h.2⟩
      rw [← h1]; exact h.1
  · rename_i h
    simp only [List.cons.injEq, true_and]
    constructor
    · intro hh; refine ⟨hh, ?_⟩; rintro ⟨h1, h2⟩; subst h1; apply h; exact ⟨hh, h2⟩
    · exact fun hh => hh.1

theorem val_norm (l : List Nat) : val (norm l) = val l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [norm_cons]
    by_cases h : norm ds = [] ∧ d = 0
    · rw [if_pos h]
      have : val ds = 0 := by rw [← ih, h.1]; rfl
      have h2 := h.2
      subst h2; simp [this]
    · rw [if_neg h]; simp only [val_cons, ih]

theorem length_norm_le (l : List Nat) : (norm l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons d ds ih =>
    rw [norm_cons]; split <;> simp <;> omega

theorem Wd_norm {l : List Nat} (h : Wd l) : Wd (norm l) := by
  induction l with
  | nil => exact Wd_nil
  | cons d ds ih =>
    rw [norm_cons]; split
    · exact Wd_nil
    · exact Wd_cons.2 ⟨(Wd_cons.1 h).1, ih (Wd_cons.1 h).2⟩

theorem normed_norm (l : List Nat) : Normed (norm l) := by
  unfold Normed
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [norm_cons]; split
    · rfl
    · rename_i h
      rw [norm_cons, ih]; simp [h]

theorem norm_eq_self {l : List Nat} (h : Normed l) : norm l = l := h

/-- `norm` keeps a prefix and everything dropped is zero. -/
theorem norm_eq_take (l : List Nat) : ∃ k, k ≤ l.length ∧ norm l = l.take k ∧ ∀ d ∈ l.drop k, d = 0 := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons d ds ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    rw [norm_cons]
    by_cases h : norm ds = [] ∧ d = 0
    · rw [if_pos h]
      refine ⟨0, by simp, rfl, ?_⟩
      intro e he
      simp only [List.drop_zero, List.mem_cons] at he
      rcases he with rfl | he
      · exact h.2
      · have : val ds = 0 := by rw [← val_norm, h.1]; rfl
        exact val_eq_zero_iff.1 this e he
    · rw [if_neg h]
      refine ⟨k + 1, by simp; omega, by simp [h1], ?_⟩
      simpa using h2

theorem norm_append_zeros (l : List Nat) (n : Nat) : norm (l ++ List.replicate n 0) = norm l := by
  induction l with
  | nil =>
    simp only [List.nil_append, norm_nil]
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, norm_cons, ih]; simp
  | cons d ds ih => rw [List.cons_append, norm_cons, norm_cons, ih]

theorem Normed.val_ge {l : List Nat} (h : Normed l) (hne : l ≠ []) (hw : Wd l) :
    2 ^ (64 * (l.length - 1)) ≤ val l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons d ds ih =>
    have hh := normed_cons.1 h
    cases ds with
    | nil =>
      have : d ≠ 0 := fun e => hh.2 ⟨rfl, e⟩
      simp; omega
    | cons e es =>
      have := ih hh.1 (by simp) (Wd_cons.1 hw).2
      simp only [List.length_cons, val_cons] at *
      have e1 : 64 * (es.length + 1 + 1 - 1) = 64 * (es.length + 1 - 1) + 64 := by omega
      rw [e1, Nat.pow_add]
      have : 2 ^ 64 * 2 ^ (64 * (es.length + 1 - 1)) ≤ 2 ^ 64 * val (e :: es) := Nat.mul_le_mul_left _ (by simpa using this)
      rw [Nat.mul_comm (2 ^ (64 * (es.length + 1 - 1))) (2 ^ 64)]
      omega

end FvModexp.Mdl
