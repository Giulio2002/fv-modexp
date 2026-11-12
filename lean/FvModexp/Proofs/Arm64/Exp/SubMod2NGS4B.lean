import FvModexp.Proofs.Arm64.Exp.SubMod2NGAlloc
import FvModexp.Proofs.Common.Util

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: `J4G` → `J5G`, the loop `for i := range z { z[i] = ^z[i] }` (nat.go:1751) on
the current array `(p, c)` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

/-- the complement loop's invariant at the test `+0x2a4` (`M0` = the memory at `J4G`) -/
@[reducible] def CI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s : State) (M0 : Memory)
    (S : State) (p c g i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat) : Prop :=
  S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) ∧ S.regs 28 = s.regs 28 ∧ S.regs 18 = s.regs 18 ∧
    S.regs 0 = BitVec.ofNat 64 p ∧ S.regs 1 = BitVec.ofNat 64 (W n) ∧ S.regs 2 = BitVec.ofNat 64 c ∧
    S.regs 3 = BitVec.ofNat 64 i ∧ S.regs 9 = BitVec.ofNat 64 n ∧
    Fw s S.mem zp zl zc yp n ∧ Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 ∧ NatLive S.mem R L3 p c ∧
    i ≤ W n ∧ natVal S.mem p i = 2 ^ (64 * i) - 1 - natVal M0 p i ∧
    (∀ j, i ≤ j → j < W n → S.mem.readLE (p + 8 * j) 8 = M0.readLE (p + 8 * j) 8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- one test of the complement loop (at `+0x2a4`) -/
theorem complIterG (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    {p c g : Nat} (hcur : CurA R L zp zc p c) (hc40 : c < 2 ^ 40) (hp64 : p < 2 ^ 64) (hWc : W n ≤ c)
    (hg : g ≤ W n) (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (M0 : Memory) (hD : natVal M0 p (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n)
    (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat)
    (hpc : S.pc = BitVec.ofNat 64 (1805584 + 0x2a4)) (hI : CI R b L zp zl zc yp yl n s M0 S p c g i L3 b3)
    (KL : ∀ (S' : State) (L' : List (Nat × Nat)) (b' : Nat), i + 1 ≤ W n →
      S'.pc = BitVec.ofNat 64 (1805584 + 0x2a4) → CI R b L zp zl zc yp yl n s M0 S' p c g (i + 1) L' b' →
      GoalG impl R b L zp zl zc yp yl n s S') :
    GoalG impl R b L zp zl zc yp yl n s S := by
  obtain ⟨hsp, h28, h18, h0, h1, h2, h3, h9, hfw, hrt, hlv, hi, hv, hhi⟩ := hI
  have hal : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have hn1 := hpre.2.2.2.2.2.2.1
  obtain ⟨hw1, -, -, -⟩ := curA_win hpre hcur
  simp only [W] at hi hD hv hhi KL h1 hWc ⊢
  obtain ⟨-, -, hacc, hp48⟩ := hlv (by omega)
  rw [show (1805584 + 0x2a4 : Nat) = 1806260 from rfl] at hpc
  unfold GoalG
  by_cases hc : i = (n + 63) / 64
  · subst hc
    janus_run until [1806268]
    refine k5 _ p c g L3 b3 hpre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrt hlv hcur hc40 hp64 hWc hg hgz hlt ?_
    all_goals try janus_simp
    simp only [W]; rw [hv, hD]
  · janus_run until [1806260]
    have hw' : S.mem.readLE (p + 8 * i) 8 = M0.readLE (p + 8 * i) 8 := hhi i (Nat.le_refl _) (by omega)
    have hnot : (~~~BitVec.ofNat 64 (S.mem.readLE (p + i * 8) 8)).toNat = 2 ^ 64 - 1 - M0.readLE (p + 8 * i) 8 := by
      rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show p + i * 8 = p + 8 * i by omega, hw']
    refine KL _ L3 b3 (by omega) ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try janus_simp
    · apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    · exact fw_fstore hfw (by omega) hal
    · exact rt_cstore hrt hcur hlv (by omega) (by omega)
    · exact natLive_store hlv _ _ _
    · simp only [W]; omega
    · rw [hnot, show p + i * 8 = p + 8 * i by omega,
        SubMod2N.compl_step _ _ _ _ _ hv (natVal_lt _ _ _) (Util.readLE8_lt _ _), natVal_succ]
    · intro j h1 h2
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hhi j (by omega) h2

theorem complG (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    {p c g : Nat} (hcur : CurA R L zp zc p c) (hc40 : c < 2 ^ 40) (hp64 : p < 2 ^ 64) (hWc : W n ≤ c)
    (hg : g ≤ W n) (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (M0 : Memory) (hD : natVal M0 p (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) :
    ∀ (k : Nat) (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - i = k →
      S.pc = BitVec.ofNat 64 (1805584 + 0x2a4) → CI R b L zp zl zc yp yl n s M0 S p c g i L3 b3 →
      GoalG impl R b L zp zl zc yp yl n s S := by
  intro k
  induction k with
  | zero =>
    intro S i L3 b3 hk hpc hI
    exact complIterG impl k5 hpre hcur hc40 hp64 hWc hg hgz hlt M0 hD S i L3 b3 hpc hI
      fun _ _ _ h => absurd h (by omega)
  | succ k ih =>
    intro S i L3 b3 hk hpc hI
    exact complIterG impl k5 hpre hcur hc40 hp64 hWc hg hgz hlt M0 hD S i L3 b3 hpc hI
      fun S' L' b' hi1 hpc' hI' => ih S' (i + 1) L' b' (by omega) hpc' hI'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s4bG (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k5 : J5G impl R b L op zp zl zc yp yl yc n s) : J4G impl R b L op zp zl zc yp yl yc n s := by
  intro S p c g L3 b3 hpre hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlv hcur hc40 hp64 hWc hg hgz hlt hv
  rw [show (1805584 + 0x28c : Nat) = 1806236 from rfl] at hpc
  unfold GoalG
  janus_run until [1806260]
  refine complG impl k5 hpre hcur hc40 hp64 hWc hg hgz hlt S.mem hv _ _ 0 L3 b3 rfl ?_
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfw, hrt, hlv, Nat.zero_le _, ?_, fun _ _ _ => rfl⟩
  all_goals try janus_simp
  have := natVal_lt S.mem p 0; rw [Nat.mul_zero, Nat.pow_zero] at this; omega

end FvModexp.Arm64.SubMod2N
