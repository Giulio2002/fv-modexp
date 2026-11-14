import FvModexp.Proofs.Amd64.Exp.W2Div
import FvModexp.Proofs.Amd64.Exp.W2Cut

set_option autoImplicit false

/-!
# window-2 prologue (amd64): what the `RR` division keeps (`keeps_div`), `ZZ.keep`, value lemmas
(agent expmc s52; twin of `Arm64.W2DivK`; the pure value lemmas are copied from it, ISA-independent)

Pure lemmas over the memory form `DvPost` of `nat.div`'s post (no machine steps).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- a normalised nat whose value is below `2^(64 n)` has at most `n` limbs -/
theorem norm_len_le {m : Memory} {p l n : Nat} (hN : NatNorm m p l) (hv : m.readLE p (8 * l) < 2 ^ (64 * n)) :
    l ≤ n := by
  refine Nat.not_lt.1 fun hc => ?_
  rcases hN with h | h
  · omega
  · have e := m.readLE_add p (8 * (l - 1)) 8
    rw [show 8 * (l - 1) + 8 = 8 * l by omega] at e
    have h1 : 1 ≤ m.readLE (p + 8 * (l - 1)) 8 := Nat.pos_of_ne_zero h
    have h2 : (256 : Nat) ^ (8 * (l - 1)) = 2 ^ (64 * (l - 1)) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega
    have h3 : 2 ^ (64 * n) ≤ 2 ^ (64 * (l - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have h4 := Nat.mul_le_mul_left (256 ^ (8 * (l - 1))) h1
    omega

/-- an odd number `> 1` does not divide a power of two -/
theorem odd_not_dvd_pow2 {M : Nat} (ho : M % 2 = 1) (h1 : 1 < M) : ∀ k, ¬ M ∣ 2 ^ k
  | 0, h => by have := Nat.le_of_dvd (by decide) h; omega
  | k + 1, ⟨c, hc⟩ => by
    have hc2 : c % 2 = 0 := by
      have h2 : (M * c) % 2 = 0 := by rw [← hc, Nat.pow_succ, Nat.mul_mod_left]
      rw [Nat.mul_mod, ho, Nat.one_mul, Nat.mod_mod] at h2; exact h2
    obtain ⟨d, rfl⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
    refine odd_not_dvd_pow2 ho h1 k ⟨d, ?_⟩
    rw [Nat.pow_succ, show M * (2 * d) = M * d * 2 by rw [Nat.mul_left_comm, Nat.mul_comm 2]] at hc
    exact Nat.eq_of_mul_eq_mul_right (by decide) hc

/-- the `RR` value `2^(128 n) mod m` is not `0` for an odd `m > 1` -/
theorem rr_pos {M n : Nat} (ho : M % 2 = 1) (h1 : 1 < M) : 0 < 2 ^ (128 * n) % M :=
  Nat.pos_of_ne_zero fun h => odd_not_dvd_pow2 ho h1 _ (Nat.dvd_of_mod_eq_zero h)

/-- a read inside the low `a + k` bytes of a value divisible by `2^(8(a+k))` is `0` -/
theorem rd_mid_zero (m : Memory) (p a k N : Nat) (h : a + k ≤ N) (hv : m.readLE p N % 2 ^ (8 * (a + k)) = 0) :
    m.readLE (p + a) k = 0 := by
  have e1 := m.readLE_add p (a + k) (N - (a + k))
  rw [show a + k + (N - (a + k)) = N by omega] at e1
  have hlt := m.readLE_lt p (a + k)
  have e256 : (256 : Nat) ^ (a + k) = 2 ^ (8 * (a + k)) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [e256] at hlt e1
  rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt] at hv
  have e2 := m.readLE_add p a k
  rw [hv] at e2
  have hp : 0 < (256 : Nat) ^ a := Nat.pow_pos (by decide)
  rcases Nat.eq_zero_of_add_eq_zero e2.symm with ⟨-, h2⟩
  rcases Nat.mul_eq_zero.1 h2 with h3 | h3
  · omega
  · exact h3

/-- `zz = 2^(128 n)` (`2n+1` limbs): its limbs `[rl, n)` are `0` -/
theorem zz_mid (m : Memory) {zzp n rl : Nat} (hv : m.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n)) (hrl : rl ≤ n) :
    m.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0 := by
  refine rd_mid_zero m zzp (8 * rl) (8 * (n - rl)) (8 * (2 * n + 1)) (by omega) ?_
  rw [hv, show 128 * n = 8 * (8 * rl + 8 * (n - rl)) + 64 * n by omega, Nat.pow_add, Nat.mul_mod_right]

set_option maxRecDepth 20000 in
/-- the facts about `zz` survive a step that keeps the accessible ranges, the live set (extended) and the stack array
(kept or fresh) -/
theorem ZZ.keep {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp n mp xp yp ylen zp zc st zzp zzc : Nat}
    {M M' : Memory} (h : ZZ R L g fs sp n mp xp yp ylen zp zc st zzp zzc M) (hx : LiveExt R L L')
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (hs : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L)) :
    ZZ R L' g fs sp n mp xp yp ylen zp zc st zzp zzc M' := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h
  exact ⟨⟨c1, c2, by rw [hacc]; exact c3, c4, hx.held c5, c6, c7, c8⟩, b2, b3, b4, b5, b6, b7, apart_arr_step b8 hs c5, b9⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `RR` division keeps the context (the scratch `RR` is the context's extra range) -/
theorem keeps_div {R : RtInv} {L L' : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r b b' costD stkD qp rrp zzp zzl rr rl rc : Nat}
    {M M' : Memory}
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [(rrp, 8 * (2 * n))] M)
    (hKD : stkD ≤ K)
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrF : Apart rrp (8 * (2 * n)) (fs - 8) 8)
    (hD : DvPost R b costD L L' b' g sp stkD st qp rrp n zzp zzl mp M M' rr rl rc) :
    Keeps R L L' g fs sp K st l0 [(rrp, 8 * (2 * n))] M M' := by
  obtain ⟨-, hce, hK, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, hcap, -, hug, huf, huw, hsu, hstg, hstf, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨-, hxD, -, -, ⟨⟨hsok', hlen', hst'⟩, hai⟩, -, hF, hL, hrg⟩ := hD
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro', f1, f2, f3, f4, f5, f6⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  obtain ⟨r8, rh, racc, r48⟩ := hrL (by omega)
  clear hLs hd hro'
  simp only [AW, Apart, stUp] at hstw huw hug huf hsu hga hstg hstf hrW hrG hrF f6
  refine keeps_of hce hxD (by simpa only [List.append_assoc] using hF) hL hrg ?_ ?_ ?_ ?_ ?_ hsok'
    (by omega) hst' ?_ hai
  · clear hstw huw hug huf hsu hga hstg hstf hrW hrG hrF f6
    intro r' hr' hlt
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
    · simp only at hlt ⊢; exact M.accessible_sub racc (Or.inr rfl) (by omega) (by omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hsu hrW huf hstf hrF f6
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hsu hrW hug hstg hrG hga
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf hrW hrG hrF f6
    intro a k' ho
    obtain ⟨-, o2, o3, o4, o5⟩ := ho
    have o6 := o5 _ (List.mem_singleton_self _)
    clear o5
    simp only [AW, Apart, stUp] at o2 o3 o4 o6
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  · clear hug huf hsu hga hstg hstf hrG hrF f6
    intro j hj
    simp only [KeptJ] at hj
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf hrW hrG hrF f6
    intro _
    have := hsok'.2.2.2.2.2.1
    simp only [stLen, stCap, stW] at hlen' this hqin ⊢; omega

end FvModexp.Amd64.W2Pro
