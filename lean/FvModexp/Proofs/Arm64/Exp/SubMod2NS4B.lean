import FvModexp.Proofs.Arm64.Exp.SubMod2NS4A
import FvModexp.Proofs.Common.Util

/-!
# `nat.subMod2N` (arm64): `J4` → `J5`, the loop `for i := range z { z[i] = ^z[i] }` (nat.go:1751) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- one test of the complement loop (at `+0x2a4`); `M0` is the memory at `J4` -/
theorem complIter (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (M0 : Memory) (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat)
    (hpc : S.pc = BitVec.ofNat 64 (1805584 + 0x2a4)) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 (W n)) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 i) (h9 : S.regs 9 = BitVec.ofNat 64 n)
    (hfw : Fw s S.mem zp zl zc yp n) (hrt : Rt R b L s zp zc n 3 S.mem L3 b3)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hD : natVal M0 zp (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) (hi : i ≤ W n)
    (hv : natVal S.mem zp i = 2 ^ (64 * i) - 1 - natVal M0 zp i)
    (hhi : ∀ j, i ≤ j → j < W n → S.mem.readLE (zp + 8 * j) 8 = M0.readLE (zp + 8 * j) 8)
    (KL : ∀ S' : State, i + 1 ≤ W n → S'.pc = BitVec.ofNat 64 (1805584 + 0x2a4) →
      S'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) → S'.regs 28 = s.regs 28 → S'.regs 18 = s.regs 18 →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 (W n) → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 3 = BitVec.ofNat 64 (i + 1) → S'.regs 9 = BitVec.ofNat 64 n →
      Fw s S'.mem zp zl zc yp n → Rt R b L s zp zc n 3 S'.mem L3 b3 →
      natVal S'.mem zp (i + 1) = 2 ^ (64 * (i + 1)) - 1 - natVal M0 zp (i + 1) →
      (∀ j, i + 1 ≤ j → j < W n → S'.mem.readLE (zp + 8 * j) 8 = M0.readLE (zp + 8 * j) 8) →
      Goal impl R b L zp zl zc yp yl n s S') :
    Goal impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, hzlive, hzw, -⟩ :=
    id hpre
  simp only [W] at hW hi hD hv hhi KL h1 ⊢
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hb' ha hw
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hacc : S.mem.accessible zp (8 * zc) true = true := (hrt.2.2.2.2.2.2 (by omega)).2.2.1
  rw [show (1805584 + 0x2a4 : Nat) = 1806260 from rfl] at hpc
  unfold Goal
  by_cases hc : i = (n + 63) / 64
  · subst hc
    janus_run until [1806268]
    refine k5 _ L3 b3 hpre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrt hlt ?_
    all_goals try janus_simp
    simp only [W]; rw [hv, hD]
  · janus_run until [1806260]
    have hw' : S.mem.readLE (zp + 8 * i) 8 = M0.readLE (zp + 8 * i) 8 := hhi i (Nat.le_refl _) (by omega)
    have hnot : (~~~BitVec.ofNat 64 (S.mem.readLE (zp + i * 8) 8)).toNat = 2 ^ 64 - 1 - M0.readLE (zp + 8 * i) 8 := by
      rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show zp + i * 8 = zp + 8 * i by omega, hw']
    refine KL _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try janus_simp
    · apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    · exact fw_zstore hfw (by omega) (by omega) hzw (by omega)
    · exact rt_zstore hpre hrt (by omega) (by omega)
    · rw [hnot, show zp + i * 8 = zp + 8 * i by omega,
        SubMod2N.compl_step _ _ _ _ _ hv (natVal_lt _ _ _) (Util.readLE8_lt _ _), natVal_succ]
    · intro j h1 h2
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hhi j (by omega) h2

theorem compl (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (M0 : Memory) : ∀ (k : Nat) (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - i = k →
    S.pc = BitVec.ofNat 64 (1805584 + 0x2a4) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 (W n) → S.regs 2 = BitVec.ofNat 64 zc →
    S.regs 3 = BitVec.ofNat 64 i → S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal M0 zp (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → i ≤ W n →
    natVal S.mem zp i = 2 ^ (64 * i) - 1 - natVal M0 zp i →
    (∀ j, i ≤ j → j < W n → S.mem.readLE (zp + 8 * j) 8 = M0.readLE (zp + 8 * j) 8) →
    Goal impl R b L zp zl zc yp yl n s S := by
  intro k
  induction k with
  | zero =>
    intro S i L3 b3 hk hpc hsp h28 h18 h0 h1 h2 h3 h9 hfw hrt hlt hD hi hv hhi
    exact complIter impl k5 hpre M0 S i L3 b3 hpc hsp h28 h18 h0 h1 h2 h3 h9 hfw hrt hlt hD hi hv hhi
      fun _ h => absurd h (by omega)
  | succ k ih =>
    intro S i L3 b3 hk hpc hsp h28 h18 h0 h1 h2 h3 h9 hfw hrt hlt hD hi hv hhi
    exact complIter impl k5 hpre M0 S i L3 b3 hpc hsp h28 h18 h0 h1 h2 h3 h9 hfw hrt hlt hD hi hv hhi
      fun S' hi1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =>
        ih S' (i + 1) L3 b3 (by omega) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hlt hD hi1 a12 a13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s4b (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k5 : J5 impl R b L op zp zl zc yp yl yc n s) : J4 impl R b L op zp zl zc yp yl yc n s := by
  intro S L3 b3 hpre hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlt hv
  rw [show (1805584 + 0x28c : Nat) = 1806236 from rfl] at hpc
  unfold Goal
  janus_run until [1806260]
  refine compl impl k5 hpre S.mem _ _ 0 L3 b3 rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrt hlt hv (Nat.zero_le _) ?_ ?_
  all_goals try janus_simp
  · omega
  · intros; trivial

end FvModexp.Arm64.SubMod2N
