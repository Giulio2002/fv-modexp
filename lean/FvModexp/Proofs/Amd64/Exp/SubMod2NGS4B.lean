import FvModexp.Proofs.Amd64.Exp.SubMod2NGAlloc

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: `J4G` → `J5G`, the loop `for i := range z { z[i] = ^z[i] }` (nat.go:1751) on
the current array `(p, c)` (agent infra s48; twin of Arm64/Exp/SubMod2NGS4B.lean)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.EvenHyp

/-- the complement loop's invariant at the test `+0x342` (`M0` = the memory at `J4G`) -/
@[reducible] def CI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s : State) (M0 : Memory)
    (S : State) (p c g i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat) : Prop :=
  S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) ∧ Abi s S ∧
    S.regs 0 = BitVec.ofNat 64 p ∧ S.regs 6 = BitVec.ofNat 64 (W n) ∧ S.regs 1 = BitVec.ofNat 64 c ∧
    S.regs 3 = BitVec.ofNat 64 i ∧ S.regs 2 = BitVec.ofNat 64 n ∧
    Fw s S.mem zp zl zc yp n ∧ Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 ∧ NatLive S.mem R L3 p c ∧
    i ≤ W n ∧ natVal S.mem p i = 2 ^ (64 * i) - 1 - natVal M0 p i ∧
    (∀ j, i ≤ j → j < W n → S.mem.readLE (p + 8 * j) 8 = M0.readLE (p + 8 * j) 8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- one test of the complement loop (at `+0x342`) -/
theorem complIterG (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    {p c g : Nat} (hcur : CurA R L zp zc p c) (hc40 : c < 2 ^ 40) (hp64 : p < 2 ^ 64) (hWc : W n ≤ c)
    (hg : g ≤ W n) (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (M0 : Memory) (hD : natVal M0 p (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n)
    (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 6216674) (hI : CI R b L zp zl zc yp yl n s M0 S p c g i L3 b3)
    (KL : ∀ (S' : State) (L' : List (Nat × Nat)) (b' : Nat), i + 1 ≤ W n →
      S'.rip = BitVec.ofNat 64 6216674 → CI R b L zp zl zc yp yl n s M0 S' p c g (i + 1) L' b' →
      GoalG impl R b L zp zl zc yp yl n s S') :
    GoalG impl R b L zp zl zc yp yl n s S := by
  obtain ⟨hsp, ⟨h14, hfs, hx15, hdf⟩, h0, h6, h1, h3, h2, hfw, hrt, hlv, hi, hv, hhi⟩ := hI
  have hs4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have hn1 := hpre.2.2.2.2.2.2.1
  have hw1 := (curA_win hpre hcur).1
  simp only [W] at hi hD hv hhi KL h6 hWc ⊢
  obtain ⟨-, -, hacc, hp48⟩ := hlv (by omega)
  have hiv : (BitVec.ofNat 64 i).toInt = i := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have hWv : (BitVec.ofNat 64 ((n + 63) / 64)).toInt = (n + 63) / 64 := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  unfold GoalG
  by_cases hc : i = (n + 63) / 64
  · subst hc
    janus64_run [hiv, hWv] until [6216679]
    refine k5 _ p c g L3 b3 hpre ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ hfw hrt hlv hcur hc40 hp64 hWc hg hgz hlt ?_
    all_goals first | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | skip
    simp only [W]; rw [hv, hD]
  · have hlt' : (i : Int) < ((n + 63) / 64 : Nat) := by omega
    janus64_run [hiv, hWv, hlt'] until [6216674]
    have hw' : S.mem.readLE (p + 8 * i) 8 = M0.readLE (p + 8 * i) 8 := hhi i (Nat.le_refl _) (by omega)
    have hnot : (~~~BitVec.ofNat 64 (S.mem.readLE (p + 8 * i) 8)).toNat = 2 ^ 64 - 1 - M0.readLE (p + 8 * i) 8 := by
      rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _), hw']
    refine KL _ L3 b3 (by omega) ?_ ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try janus64_simp
    all_goals first
      | exact h14 | exact hfs | exact hx15 | exact hdf
      | exact fw_cstore hfw (by omega) hs4
      | exact rt_cstore hrt hcur hlv (by omega) (by omega)
      | exact natLive_store hlv _ _ _
      | (simp only [W]; omega)
      | omega
      | (try rw [show p + i * 8 = p + 8 * i by omega]
         rw [hnot, SubMod2N.compl_step _ _ _ _ _ hv (natVal_lt _ _ _) (Util.readLE8_lt _ _), natVal_succ])
      | (intro j h1 h2
         rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
         exact hhi j (by omega) h2)
      | skip

theorem complG (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    {p c g : Nat} (hcur : CurA R L zp zc p c) (hc40 : c < 2 ^ 40) (hp64 : p < 2 ^ 64) (hWc : W n ≤ c)
    (hg : g ≤ W n) (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (M0 : Memory) (hD : natVal M0 p (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) :
    ∀ (k : Nat) (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - i = k →
      S.rip = BitVec.ofNat 64 6216674 → CI R b L zp zl zc yp yl n s M0 S p c g i L3 b3 →
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
set_option maxHeartbeats 16000000 in
theorem s4bG (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k5 : J5G impl R b L op zp zl zc yp yl yc n s) : J4G impl R b L op zp zl zc yp yl yc n s := by
  intro S p c g L3 b3 hpre hpc hsp hab h0 h6 h1 h2 hfw hrt hlv hcur hc40 hp64 hWc hg hgz hlt hv
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  unfold GoalG
  janus64_run until [6216674]
  refine complG impl k5 hpre hcur hc40 hp64 hWc hg hgz hlt S.mem hv _ _ 0 L3 b3 rfl ?_
    ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hfw, hrt, hlv, Nat.zero_le _, ?_, fun _ _ _ => rfl⟩
  all_goals first
    | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf
    | (have := natVal_lt S.mem p 0; rw [Nat.mul_zero, Nat.pow_zero] at this; omega)
    | janus64_simp

end FvModexp.Amd64.SubMod2N
