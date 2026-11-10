import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.NatBasic

/-!
# Bridge from memory limbs to the mathdiv limb-list models (`FvModexp.Mdl`, docs/MODELS.md)

`limbs m p n` is the Go slice `p[0:n]` of 64-bit words in memory `m` as the model's `List Nat` (least significant first).
Its value is `lv m p n` (`val_limbs`), every element is a word (`Wd_limbs`). Two word lists of the same length with the
same value are equal (`eq_of_val`), so the value-level summaries of the assembly kernels (`lv`, model independent) give
the model-level statements (`limbs m' z n = (Mdl.addVV (limbs m x n) (limbs m y n)).1`, ...) proved here once for all ISAs.
-/

open Janus Janus.Arm64

namespace FvModexp.Asm

/-- the `n` words at `p`, least significant first (the model's `nat`) -/
def limbs (m : Memory) (p : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => m.readLE p 8 :: limbs m (p + 8) n

@[simp] theorem length_limbs (m : Memory) (p n : Nat) : (limbs m p n).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [limbs, ih]

theorem Wd_limbs (m : Memory) (p n : Nat) : Mdl.Wd (limbs m p n) := by
  induction n generalizing p with
  | zero => exact Mdl.Wd_nil
  | succ n ih => exact Mdl.Wd_cons.2 ⟨limb_lt m p, ih _⟩

theorem val_limbs (m : Memory) (p n : Nat) : Mdl.val (limbs m p n) = lv m p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [limbs, Mdl.val, ih, lv]
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Memory.readLE_add]

/-- word lists of the same length are determined by their values -/
theorem eq_of_val : ∀ {a b : List Nat}, Mdl.Wd a → Mdl.Wd b → a.length = b.length → Mdl.val a = Mdl.val b → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: xs, b :: ys, ha, hb, hl, hv => by
    have ha' := Mdl.Wd_cons.1 ha
    have hb' := Mdl.Wd_cons.1 hb
    simp only [Mdl.val] at hv
    have h1 : a = b := by omega
    have h2 : Mdl.val xs = Mdl.val ys := by omega
    rw [h1, eq_of_val ha'.2 hb'.2 (by simpa using hl) h2]

/-- a value and a carry are determined by `v + P c` when `v < P` -/
theorem split_unique {P v c v' c' : Nat} (hv : v < P) (hv' : v' < P) (h : v + P * c = v' + P * c') :
    v = v' ∧ c = c' := by
  have hP : 0 < P := by omega
  have e1 : (v + P * c) % P = v := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  have e2 : (v' + P * c') % P = v' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv']
  have e3 : (v + P * c) / P = c := by rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hv]; simp
  have e4 : (v' + P * c') / P = c' := by rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hv']; simp
  refine ⟨?_, ?_⟩
  · rw [← e1, ← e2, h]
  · rw [← e3, ← e4, h]

/-- `addVV` (assembly, value form) agrees with the model `Mdl.addVV` (arith.go:63 `addVV_g`) -/
theorem addVV_model (m m' : Memory) (z x y n c : Nat)
    (hz : lv m' z n = (lv m x n + lv m y n) % 2 ^ (64 * n)) (hc : c = (lv m x n + lv m y n) / 2 ^ (64 * n)) :
    limbs m' z n = (Mdl.addVV (limbs m x n) (limbs m y n)).1 ∧ c = (Mdl.addVV (limbs m x n) (limbs m y n)).2 := by
  obtain ⟨hl, hw, -, hv⟩ := Mdl.addVVc_spec (limbs m x n) (limbs m y n) 0 (Wd_limbs m x n) (Wd_limbs m y n) (by simp) (by omega)
  simp only [length_limbs, val_limbs, Nat.add_zero] at hl hv
  have hP : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have hlt := Mdl.val_lt hw
  rw [hl] at hlt
  have hzv : lv m' z n + 2 ^ (64 * n) * c = lv m x n + lv m y n := by
    rw [hz, hc]; exact Nat.mod_add_div _ _
  obtain ⟨e1, e2⟩ := split_unique (lv_lt m' z n) hlt (hzv.trans hv.symm)
  refine ⟨eq_of_val (Wd_limbs m' z n) hw (by simp only [length_limbs, Mdl.addVV, Mdl.subVV]; exact hl.symm) ?_, e2⟩
  rw [val_limbs]; exact e1

/-- `subVV` (assembly, value form: `Z + Y = X + 2^(64 n) b`, `b ≤ 1`) agrees with the model `Mdl.subVV` (arith.go:77) -/
theorem subVV_model (m m' : Memory) (z x y n b : Nat) (hb : b ≤ 1)
    (hz : lv m' z n + lv m y n = lv m x n + 2 ^ (64 * n) * b) :
    limbs m' z n = (Mdl.subVV (limbs m x n) (limbs m y n)).1 ∧ b = (Mdl.subVV (limbs m x n) (limbs m y n)).2 := by
  obtain ⟨hl, hw, hb', hv⟩ := Mdl.subVVc_spec (limbs m x n) (limbs m y n) 0 (Wd_limbs m x n) (Wd_limbs m y n) (by simp)
    (by omega)
  simp only [length_limbs, val_limbs, Nat.add_zero] at hl hv
  have hlt := Mdl.val_lt hw
  rw [hl] at hlt
  have hZ := lv_lt m' z n
  have hY := lv_lt m y n
  -- both borrows are the comparison `X < Y`
  have hb1 : b = (Mdl.subVV (limbs m x n) (limbs m y n)).2 := by
    unfold Mdl.subVV
    rcases Nat.lt_or_ge (lv m x n) (lv m y n) with h | h
    · have : b = 1 := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0; omega
        · omega
      have : (Mdl.subVVc (limbs m x n) (limbs m y n) 0).2 = 1 := by
        rcases Nat.eq_zero_or_pos (Mdl.subVVc (limbs m x n) (limbs m y n) 0).2 with h0 | h0
        · rw [h0] at hv; omega
        · omega
      omega
    · have : b = 0 := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · exact h0
        · have : b = 1 := by omega
          subst this; omega
      have : (Mdl.subVVc (limbs m x n) (limbs m y n) 0).2 = 0 := by
        rcases Nat.eq_zero_or_pos (Mdl.subVVc (limbs m x n) (limbs m y n) 0).2 with h0 | h0
        · exact h0
        · have e : (Mdl.subVVc (limbs m x n) (limbs m y n) 0).2 = 1 := by omega
          rw [e] at hv; omega
      omega
  refine ⟨eq_of_val (Wd_limbs m' z n) hw (by simp only [length_limbs, Mdl.addVV, Mdl.subVV]; exact hl.symm) ?_, hb1⟩
  rw [val_limbs]
  unfold Mdl.subVV at hb1 ⊢
  rw [← hb1] at hv
  omega

/-- `nat.cmp`'s result word (lengths first, then values) is the model `Mdl.natCmp` (nat.go:152) as a 64-bit word -/
theorem cmp_model (m : Memory) (x y lx ly : Nat) (r : BitVec 64)
    (hr : r = if lx < ly then 18446744073709551615#64 else if ly < lx then 1#64
      else if lv m x lx < lv m y ly then 18446744073709551615#64 else if lv m y ly < lv m x lx then 1#64 else 0#64) :
    r = BitVec.ofInt 64 (Mdl.natCmp (limbs m x lx) (limbs m y ly)) := by
  subst hr
  unfold Mdl.natCmp
  simp only [length_limbs]
  by_cases h : lx ≠ ly ∨ lx = 0
  · rw [if_pos h]
    by_cases h1 : lx < ly
    · simp [h1]; try rfl
    · by_cases h2 : ly < lx
      · simp [h1, h2]; try rfl
      · have e : lx = ly := by omega
        subst e
        have h0 : lx = 0 := by omega
        subst h0
        simp [lv_zero]; try rfl
  · rw [if_neg h]
    have e : lx = ly := by omega
    subst e
    have hne : limbs m x lx ≠ [] := by intro hh; have := congrArg List.length hh; simp at this; omega
    rw [Mdl.cmpRev_spec _ _ (fun d hd => Wd_limbs m x lx d (List.mem_reverse.1 hd)) (fun d hd => Wd_limbs m y lx d (List.mem_reverse.1 hd))
      (by simp) (by simpa using hne)]
    rw [← Mdl.val_reverse, ← Mdl.val_reverse, List.reverse_reverse, List.reverse_reverse, val_limbs, val_limbs]
    simp only [Nat.lt_irrefl, if_false, Mdl.cmpInt]
    by_cases h1 : lv m x lx < lv m y lx
    · simp [h1]; try rfl
    · by_cases h2 : lv m y lx < lv m x lx
      · simp [h1, h2]; try rfl
      · simp [h1, h2]; try rfl

/-- a memory slice and a carry with the same value as a model output of the same length are that output -/
theorem limbs_of_value (m' : Memory) (z n c : Nat) (L : List Nat) (c' : Nat) (hL : Mdl.Wd L) (hlen : L.length = n)
    (h : lv m' z n + 2 ^ (64 * n) * c = Mdl.val L + 2 ^ (64 * n) * c') : limbs m' z n = L ∧ c = c' := by
  have hlt := Mdl.val_lt hL
  rw [hlen] at hlt
  obtain ⟨e1, e2⟩ := split_unique (lv_lt m' z n) hlt h
  exact ⟨eq_of_val (Wd_limbs m' z n) hL (by simp [hlen]) (by rw [val_limbs]; exact e1), e2⟩

/-- `mulAddVWW` (value form `Z + 2^(64 n) c = X·y + r`) agrees with the model `Mdl.mulAddVWW` (arith.go:244) -/
theorem mulAddVWW_model (m m' : Memory) (z x n y r c : Nat) (hy : y < 2 ^ 64) (hr : r < 2 ^ 64)
    (h : lv m' z n + 2 ^ (64 * n) * c = lv m x n * y + r) :
    limbs m' z n = (Mdl.mulAddVWW (limbs m x n) y r).1 ∧ c = (Mdl.mulAddVWW (limbs m x n) y r).2 := by
  obtain ⟨hl, hw, -, hv⟩ := Mdl.mulAddVWW_spec (limbs m x n) y r (Wd_limbs m x n) hy hr
  simp only [length_limbs, val_limbs] at hl hv
  exact limbs_of_value m' z n c _ _ hw hl (by rw [h, hv])

/-- `addMulVVWW` (value form `Z + 2^(64 n) c = X + Y·m + a`) agrees with the model `Mdl.addMulVVWW` (arith.go:255) -/
theorem addMulVVWW_model (m0 m' : Memory) (z x y n mv a c : Nat) (hm : mv < 2 ^ 64) (ha : a < 2 ^ 64)
    (h : lv m' z n + 2 ^ (64 * n) * c = lv m0 x n + lv m0 y n * mv + a) :
    limbs m' z n = (Mdl.addMulVVWW (limbs m0 x n) (limbs m0 y n) mv a).1 ∧
      c = (Mdl.addMulVVWW (limbs m0 x n) (limbs m0 y n) mv a).2 := by
  obtain ⟨hl, hw, -, hv⟩ := Mdl.addMulVVWW_spec (limbs m0 x n) (limbs m0 y n) mv a (Wd_limbs m0 x n) (Wd_limbs m0 y n)
    (by simp) hm ha
  simp only [length_limbs, val_limbs] at hl hv
  exact limbs_of_value m' z n c _ _ hw hl (by rw [h, hv])

end FvModexp.Asm
