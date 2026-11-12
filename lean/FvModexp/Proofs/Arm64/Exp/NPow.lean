import FvModexp.Proofs.Arm64.Exp.NDisp
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64): `m.isPow2()` (nat.go:376-388, inlined at fn+0x578..0x5c0) → `expNNPowerOfTwo` entry

For `m = 2^(64(n-1) + e)` (normalised: words `0..n-2` zero, word `n-1 = 2^e`): the loop skips the zero words (no
`panicBounds`: the top word is non-zero), the test `i == len(m)-1 && x&(x-1) == 0` succeeds, `logM = 64 i + ctz(x)`
(`RBIT; CLZ`), and `expNNPowerOfTwo` is called with `X10 = logM`, `X1 = n` (return fn+0x5d0).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

theorem rbitNat_zero : ∀ n, rbitNat n 0 = 0
  | 0 => rfl
  | n + 1 => by simp only [rbitNat, Nat.zero_mod, Nat.zero_div, Nat.zero_mul, Nat.zero_add]; exact rbitNat_zero n

theorem rbitNat_pow : ∀ n e, e < n → rbitNat n (2 ^ e) = 2 ^ (n - 1 - e)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    rcases e with _ | e
    · simp only [rbitNat, Nat.pow_zero, Nat.one_mod, Nat.one_mul]
      rw [show (1 : Nat) / 2 = 0 by decide, rbitNat_zero, Nat.add_zero, show n + 1 - 1 - 0 = n by omega]
    · have h2 : 2 ^ (e + 1) % 2 = 0 := by rw [Nat.pow_succ]; exact Nat.mul_mod_left _ _
      have h3 : 2 ^ (e + 1) / 2 = 2 ^ e := by rw [Nat.pow_succ]; exact Nat.mul_div_cancel _ (by decide)
      simp only [rbitNat, h2, h3, Nat.zero_mul, Nat.zero_add]
      rw [rbitNat_pow n e (by omega)]
      congr 1; omega

theorem clzNat_pow : ∀ n j, j < n → clzNat n (2 ^ j) = n - 1 - j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    simp only [clzNat, Nat.testBit_two_pow]
    by_cases hj : j = n
    · subst hj; simp
    · rw [if_neg (by simpa [eq_comm] using hj), clzNat_pow n j (by omega)]; omega

/-- `RBIT; CLZ` of `2^e` is `e` -/
theorem ctz_pow (e : Nat) (he : e < 64) : clzNat 64 (rbitNat 64 (2 ^ e)) = e := by
  rw [rbitNat_pow 64 e he, clzNat_pow 64 _ (by omega)]; omega

theorem pow_and_pred (e : Nat) : 2 ^ e &&& (2 ^ e - 1) = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_self _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem powStep (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (mp n e i : Nat) (M : Memory) (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true)
    (hi : i + 1 ≤ n) (he : e < 64)
    (hw : M.readLE (mp + 8 * i) 8 = if i + 1 = n then 2 ^ e else 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 powH) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h13 : S.regs 13 = BitVec.ofNat 64 i) (hmem : S.mem = M)
    (KN : i + 1 < n → ∀ S' : State, S'.pc = BitVec.ofNat 64 powH → S'.sp = S.sp →
      (∀ r, r ≠ 13 → r ≠ 15 → S'.regs r = S.regs r) → S'.regs 13 = BitVec.ofNat 64 (i + 1) → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KP : i + 1 = n → ∀ S' : State, S'.pc = BitVec.ofNat 64 p2A → S'.sp = S.sp →
      (∀ r, r ≠ 1 → r ≠ 10 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 30 → S'.regs r = S.regs r) →
      S'.regs 1 = S.regs 11 → S'.regs 10 = BitVec.ofNat 64 (64 * i + e) →
      S'.regs 30 = BitVec.ofNat 64 1788032 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have ha : M.accessible (mp + 8 * i) 8 false = true := Memory.accessible_mono _ hma (by omega) (by omega)
  have hpe : 2 ^ e < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) he
  have hn48 : n ≤ 2 ^ 45 := by omega
  by_cases hl : i + 1 = n
  · rw [if_pos hl] at hw
    subst hl
    have hw' : M.readLE (mp + i * 8) 8 = 2 ^ e := by rw [Nat.mul_comm]; exact hw
    have hc : clzNat 64 (rbitNat 64 (2 ^ e) % 18446744073709551616) = e := by
      have hr := rbitNat_pow 64 e he
      rw [hr, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (show 64 - 1 - e < 64 by omega)),
        clzNat_pow 64 _ (by omega)]; omega
    have ha3 : 2 ^ e - 1 &&& 2 ^ e = 0 := by rw [Nat.and_comm, pow_and_pred]
    have hpz : 2 ^ e ≠ 0 := Nat.pos_iff_ne_zero.1 Nat.one_le_two_pow
    janus_run [hw', hc, ha3] until [p2A, 1788008, 1787944]
    refine KP rfl _ rfl rfl (fun r h1 h2 h3 h4 h5 h6 => ?_) ?_ ?_ ?_ rfl
    · simp only [setReg, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]
    all_goals first | (janus_simp; done) | skip
    all_goals simp (config := { decide := true }) only [setReg, ite_true, ite_false, hc]
    all_goals apply BitVec.eq_of_toNat_eq
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    all_goals omega
  · rw [if_neg hl] at hw
    have hw' : M.readLE (mp + i * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hw
    janus_run [hw'] until [powH, 1788008, 1788084]
    refine KN (by omega) _ rfl rfl (fun r h1 h2 => ?_) ?_ rfl
    · simp only [setReg, if_neg h1, if_neg h2]
    all_goals first | (janus_simp; done) | skip
    all_goals simp (config := { decide := true }) only [setReg, ite_true, ite_false]
    all_goals apply BitVec.eq_of_toNat_eq
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    all_goals omega

/-- the whole `isPow2` loop from `i` (words `i..n-2` zero, word `n-1 = 2^e`) to `expNNPowerOfTwo`'s entry -/
theorem powAll (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (mp n e : Nat) (M : Memory) (sp0 : BitVec 64) (G : Nat → BitVec 64)
    (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true) (he : e < 64)
    (hw : ∀ j, j < n → M.readLE (mp + 8 * j) 8 = if j + 1 = n then 2 ^ e else 0)
    (h1 : G 1 = BitVec.ofNat 64 n) (h10 : G 10 = BitVec.ofNat 64 mp)
    (KP : ∀ S' : State, S'.pc = BitVec.ofNat 64 p2A → S'.sp = sp0 →
      (∀ r, r ≠ 1 → r ≠ 10 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 30 → S'.regs r = G r) →
      S'.regs 1 = G 11 → S'.regs 10 = BitVec.ofNat 64 (64 * (n - 1) + e) →
      S'.regs 30 = BitVec.ofNat 64 1788032 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    ∀ d i (S : State), n - 1 - i = d → i < n → S.pc = BitVec.ofNat 64 powH → S.sp = sp0 →
      (∀ r, r ≠ 13 → r ≠ 15 → r ≠ 16 → S.regs r = G r) → S.regs 13 = BitVec.ofNat 64 i → S.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hpc hsp hG h13 hmem
    refine powStep impl ret0 hret Q mp n e i M hmp hma (by omega) he (hw i hi) S hpc
      ((hG 1 (by decide) (by decide) (by decide)).trans h1) ((hG 10 (by decide) (by decide) (by decide)).trans h10) h13
      hmem (fun h => absurd h (by omega)) (fun hl S' e1 e2 e3 e4 e5 e6 e7 => KP S' e1 (e2.trans hsp) (fun r a b c d f g => ?_)
        (e4.trans (hG 11 (by decide) (by decide) (by decide))) (by rw [e5]; congr 2; omega) e6 e7)
    rw [e3 r a b c d f g, hG r c d f]
  | succ d ih =>
    intro i S hd hi hpc hsp hG h13 hmem
    refine powStep impl ret0 hret Q mp n e i M hmp hma (by omega) he (hw i hi) S hpc
      ((hG 1 (by decide) (by decide) (by decide)).trans h1) ((hG 10 (by decide) (by decide) (by decide)).trans h10) h13
      hmem (fun hl S' e1 e2 e3 e4 e5 => ih (i + 1) S' (by omega) hl e1 (e2.trans hsp)
        (fun r a b c => (e3 r a b).trans (hG r a b c)) e4 e5) (fun hl => absurd hl (by omega))

end FvModexp.Arm64.ExpN
