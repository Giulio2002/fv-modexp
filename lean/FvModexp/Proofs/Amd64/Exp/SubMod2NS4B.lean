import FvModexp.Proofs.Amd64.Exp.SubMod2NS4A
import FvModexp.Proofs.Common.Util

/-!
# `nat.subMod2N` (amd64): `J4` → `J5`, the loop `for i := range z { z[i] = ^z[i] }` (nat.go:1751) (agent infra)

Loop head `+0x342` (`CMPQ BX, SI; JL`): `RAX = zp`, `RBX = i`, `RSI = ⌈n/64⌉`, `RCX = zc`, `RDX = n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- one test of the complement loop (at `+0x342`); `M0` is the memory at `J4` -/
theorem complIter (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (M0 : Memory) (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 6216674) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128))
    (hab : Abi s S)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h6 : S.regs 6 = BitVec.ofNat 64 (W n)) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 i) (h2 : S.regs 2 = BitVec.ofNat 64 n)
    (hfw : Fw s S.mem zp zl zc yp n) (hrt : Rt R b L s zp zc n 3 S.mem L3 b3)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hD : natVal M0 zp (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) (hi : i ≤ W n)
    (hv : natVal S.mem zp i = 2 ^ (64 * i) - 1 - natVal M0 zp i)
    (hhi : ∀ j, i ≤ j → j < W n → S.mem.readLE (zp + 8 * j) 8 = M0.readLE (zp + 8 * j) 8)
    (KL : ∀ S' : State, i + 1 ≤ W n → S'.rip = BitVec.ofNat 64 6216674 →
      S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S' →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 6 = BitVec.ofNat 64 (W n) → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 3 = BitVec.ofNat 64 (i + 1) → S'.regs 2 = BitVec.ofNat 64 n →
      Fw s S'.mem zp zl zc yp n → Rt R b L s zp zc n 3 S'.mem L3 b3 →
      natVal S'.mem zp (i + 1) = 2 ^ (64 * (i + 1)) - 1 - natVal M0 zp (i + 1) →
      (∀ j, i + 1 ≤ j → j < W n → S'.mem.readLE (zp + 8 * j) 8 = M0.readLE (zp + 8 * j) 8) →
      Goal impl R b L zp zl zc yp yl n s S') :
    Goal impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, -, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, hzlive, hzw, -⟩ :=
    id hpre
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  simp only [W] at hW hi hD hv hhi KL h6 ⊢
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hb' ha hw
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hacc : S.mem.accessible zp (8 * zc) true = true := (hrt.2.2.2.2.2.2 (by omega)).2.2.1
  have hiv : (BitVec.ofNat 64 i).toInt = i := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have hWv : (BitVec.ofNat 64 ((n + 63) / 64)).toInt = (n + 63) / 64 := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  unfold Goal
  by_cases hc : i = (n + 63) / 64
  · subst hc
    janus64_run [hiv, hWv] until [6216679]
    refine k5 _ L3 b3 hpre ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ hfw hrt hlt ?_
    all_goals first | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | skip
    rw [hv, hD]
  · have hlt' : (i : Int) < ((n + 63) / 64 : Nat) := by omega
    janus64_run [hiv, hWv, hlt'] until [6216674]
    have hw' : S.mem.readLE (zp + 8 * i) 8 = M0.readLE (zp + 8 * i) 8 := hhi i (Nat.le_refl _) (by omega)
    refine KL _ (by omega) ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp; exact hfs
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · exact fw_zstore hfw (by omega) (by omega) hzw (by omega)
    · exact rt_zstore hpre hrt (by omega) (by omega)
    · try rw [show zp + i * 8 = zp + 8 * i by omega]
      have hnot : (~~~BitVec.ofNat 64 (S.mem.readLE (zp + 8 * i) 8)).toNat = 2 ^ 64 - 1 - M0.readLE (zp + 8 * i) 8 := by
        rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _), hw']
      rw [hnot, SubMod2N.compl_step _ _ _ _ _ hv (natVal_lt _ _ _) (Util.readLE8_lt _ _), natVal_succ]
    · intro j h1 h2
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hhi j (by omega) h2

theorem compl (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k5 : J5 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (M0 : Memory) : ∀ (k : Nat) (S : State) (i : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - i = k →
    S.rip = BitVec.ofNat 64 6216674 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 6 = BitVec.ofNat 64 (W n) → S.regs 1 = BitVec.ofNat 64 zc →
    S.regs 3 = BitVec.ofNat 64 i → S.regs 2 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal M0 zp (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → i ≤ W n →
    natVal S.mem zp i = 2 ^ (64 * i) - 1 - natVal M0 zp i →
    (∀ j, i ≤ j → j < W n → S.mem.readLE (zp + 8 * j) 8 = M0.readLE (zp + 8 * j) 8) →
    Goal impl R b L zp zl zc yp yl n s S := by
  intro k
  induction k with
  | zero =>
    intro S i L3 b3 hk hpc hsp hab h0 h6 h1 h3 h2 hfw hrt hlt hD hi hv hhi
    exact complIter impl k5 hpre M0 S i L3 b3 hpc hsp hab h0 h6 h1 h3 h2 hfw hrt hlt hD hi hv hhi
      fun _ h => absurd h (by omega)
  | succ k ih =>
    intro S i L3 b3 hk hpc hsp hab h0 h6 h1 h3 h2 hfw hrt hlt hD hi hv hhi
    exact complIter impl k5 hpre M0 S i L3 b3 hpc hsp hab h0 h6 h1 h3 h2 hfw hrt hlt hD hi hv hhi
      fun S' hi1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =>
        ih S' (i + 1) L3 b3 (by omega) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hlt hD hi1 a11 a12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s4b (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k5 : J5 impl R b L op zp zl zc yp yl yc n s) : J4 impl R b L op zp zl zc yp yl yc n s := by
  intro S L3 b3 hpre hpc hsp hab h0 h6 h1 h2 hfw hrt hlt hv
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  unfold Goal
  janus64_run until [6216674]
  refine compl impl k5 hpre S.mem _ _ 0 L3 b3 rfl ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ hfw hrt hlt hv (Nat.zero_le _) ?_ ?_
  all_goals first
    | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | (intros; trivial)
    | (have := natVal_lt S.mem zp 0; rw [Nat.mul_zero, Nat.pow_zero] at this; omega)
    | (intro j _ _; janus64_simp)

end FvModexp.Amd64.SubMod2N
