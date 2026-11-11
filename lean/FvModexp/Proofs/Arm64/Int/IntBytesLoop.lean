import FvModexp.Proofs.Arm64.Int.IntBytesSkip
import FvModexp.Proofs.Common.AsmDivNat

/-! # `(*Int).Bytes` (arm64): the byte loops of `nat.bytes` (`for _, d := range z { for j := 0; j < 8; j++ {…} }`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.IntBytes

/-- `LSR $8` (as `UBFM`): the value divided by `256`. -/
theorem lsr8_val (D : BitVec 64) :
    (D.rotateRight 8 &&& 18446744073709551615#64 &&& 72057594037927935#64).toNat = D.toNat / 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_rotateRight]
  simp only [show 8 % 64 = 8 from rfl, show 64 - 8 = 56 from rfl, BitVec.toNat_ofNat]
  have hv := D.isLt
  have e1 : D.toNat <<< 56 % 2 ^ 64 = (D.toNat % 2 ^ 8) * 2 ^ 56 := by rw [Nat.shiftLeft_eq]; omega
  have hA : D.toNat >>> 8 < 2 ^ 56 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [e1, Nat.or_comm, FvModexp.AsmDiv.or_hi_comm _ _ _ hA, Nat.shiftRight_eq_div_pow]
  rw [show ((2 : Nat) ^ 64 - 1) % 2 ^ 64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (72057594037927935 : Nat) % 2 ^ 64 = 2 ^ 56 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The byte `MOVB` stores. -/
theorem byte_of_read (m : Memory) (a n : Nat) : m.readLE a (n + 1) % 256 = (m.bytes a).toNat := by
  rw [Memory.readLE_succ]; have := (m.bytes a).isLt; omega

theorem read_div (m : Memory) (a n : Nat) : m.readLE a (n + 1) / 256 = m.readLE (a + 1) n := by
  rw [Memory.readLE_succ]; have := (m.bytes a).isLt; omega

set_option maxRecDepth 20000 in
/-- The inner loop of word `k`: bytes `8k + j … 8k + 7` of `abs` stored at buffer indices `N-1-(8k+j)` down. -/
theorem innerLoop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (q ap N : Nat) (L' : List (Nat × Nat)) (b' : Nat) (hN1 : N ≤ 1024) (hN8 : N % 8 = 0)
    (hsp : 4160 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 16) true = true)
    (k : Nat) (hk8 : 8 * k + 8 ≤ N)
    (hcont : ∀ (S : State) (m' : Memory), Inv R b L x s ret q ap N (8 * (k + 1)) L' b' m' →
      S.pc = BitVec.ofNat 64 hOuter → S.sp = s.sp - 64#64 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 N → S.regs 2 = BitVec.ofNat 64 (k + 1) → S.regs 3 = BitVec.ofNat 64 ap →
      S.regs 4 = BitVec.ofNat 64 (N / 8) → S.regs 5 = BitVec.ofNat 64 (N / 8) →
      S.regs 6 = BitVec.ofNat 64 (N - 8 * (k + 1)) → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m' →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L x s s')) :
    ∀ r (S : State) (m : Memory) (J D : BitVec 64), J.toNat + r = 8 → Inv R b L x s ret q ap N (8 * k + J.toNat) L' b' m →
      D.toNat = s.mem.readLE (ap + (8 * k + J.toNat)) (8 - J.toNat) →
      S.pc = BitVec.ofNat 64 hInner → S.sp = s.sp - 64#64 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 N → S.regs 2 = BitVec.ofNat 64 k → S.regs 3 = BitVec.ofNat 64 ap →
      S.regs 4 = BitVec.ofNat 64 (N / 8) → S.regs 5 = BitVec.ofNat 64 (N / 8) →
      S.regs 6 = BitVec.ofNat 64 (N - (8 * k + J.toNat)) → S.regs 7 = D → S.regs 8 = J →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L x s s') := by
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  have h88 : N / 8 * 8 = N := by omega
  intro r
  induction r with
  | zero =>
    intro S m J D hJ hI hD hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr28 hr18 hm
    have hJ8 : J.toNat = 8 := by omega
    janus_run [h88] until [hOuter]
    refine hcont _ m (by rw [show 8 * (k + 1) = 8 * k + J.toNat by omega]; exact hI) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals janus_simp
    all_goals first
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | rw [show N - 8 * (k + 1) = N - (8 * k + J.toNat) by omega]
  | succ r ih =>
    intro S m J D hJ hI hD hpc hsp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr28 hr18 hm
    have hI' := hI
    obtain ⟨hm1, hm2, -, hN0, hq48, hqacc, -, -, -, -, -, -, -, -, -, hfr, -⟩ := hI'
    have hJ8 : J.toNat < 8 := by omega
    have ht : 8 * k + J.toNat < N := by omega
    have hneg : (BitVec.ofNat 64 (N - (8 * k + J.toNat)) - 1#64).getLsbD 63 = false := by
      rw [BitVec.getLsbD_last, BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
    janus_run [h88, hneg] until [hInner]
    have hst := Inv.store hI ht D.toNat (by
      rw [hD, show 8 - J.toNat = (8 - J.toNat - 1) + 1 by omega, byte_of_read])
    have hJ1 : (J + 1#64).toNat = J.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    rw [show N - (8 * k + J.toNat) - 1 = N - 1 - (8 * k + J.toNat) by omega]
    refine ih _ _ (J + 1#64) (D.rotateRight 8 &&& 18446744073709551615#64 &&& 72057594037927935#64) (by omega)
      (by rw [hJ1, ← Nat.add_assoc]; exact hst) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [lsr8_val, hD, hJ1, show 8 - J.toNat = (8 - (J.toNat + 1)) + 1 by omega, read_div]
      rw [show ap + (8 * k + J.toNat) + 1 = ap + (8 * k + (J.toNat + 1)) by omega]
    all_goals janus_simp
    all_goals first
      | rfl
      | (apply BitVec.eq_of_toNat_eq; simp; omega)

set_option maxRecDepth 20000 in
/-- The outer loop over the words `k … al - 1`, then the zero-skip loop and the return. -/
theorem outerLoop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (q ap N : Nat) (L' : List (Nat × Nat)) (b' : Nat) (hN1 : N ≤ 1024)
    (hap : ap = s.mem.readLE (x.toNat + 8) 8) (hN : N = 8 * s.mem.readLE (x.toNat + 16) 8)
    (hapacc : s.mem.accessible ap N false = true) (hap48 : ap + N ≤ 2 ^ 48)
    (hsp : 4160 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 16) true = true) :
    ∀ r (S : State) (m : Memory) (k : Nat), k + r = N / 8 → Inv R b L x s ret q ap N (8 * k) L' b' m →
      S.pc = BitVec.ofNat 64 hOuter → S.sp = s.sp - 64#64 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 N → S.regs 2 = BitVec.ofNat 64 k → S.regs 3 = BitVec.ofNat 64 ap →
      S.regs 4 = BitVec.ofNat 64 (N / 8) → S.regs 5 = BitVec.ofNat 64 (N / 8) →
      S.regs 6 = BitVec.ofNat 64 (N - 8 * k) → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L x s s') := by
  have hN8 : N % 8 = 0 := by omega
  have h88 : N / 8 * 8 = N := by omega
  have hsp' := hsp
  obtain ⟨hs1, hs2, hs3⟩ := hsp'
  intro r
  induction r with
  | zero =>
    intro S m k hk hI hpc hsp0 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr28 hr18 hm
    have hkN : 8 * k = N := by omega
    have h0 : BitVec.ofNat 64 (N - 8 * k) = 0#64 := by rw [hkN, Nat.sub_self]
    rw [h0] at hr6
    janus_run [h88] until [hSkip]
    refine skipLoop impl R b L x ret hret s q ap N L' b' m (by have := hI; rwa [hkN] at this) hap hN hN1 hsp hw N _ 0#64
      (by simp) (fun j hj => absurd hj (by simp)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals janus_simp
    all_goals first | rfl | (apply BitVec.eq_of_toNat_eq; simp; omega)
  | succ r ih =>
    intro S m k hk hI hpc hsp0 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr28 hr18 hm
    have hI' := hI
    obtain ⟨hm1, hm2, habs, hN0, hq48, hqacc, -, -, -, -, -, -, -, -, -, hfr, -⟩ := hI'
    have hkl : 8 * k + 8 ≤ N := by omega
    have hrd : m.readLE (ap + 8 * k) 8 = s.mem.readLE (ap + 8 * k) 8 := habs _ _ (by omega) (by omega)
    janus_run [h88, hrd] until [hInner]
    refine innerLoop impl R b L x ret hret s q ap N L' b' hN1 hN8 hsp hw k hkl
      (fun S' m' hI' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
        ih S' m' (k + 1) (by omega) hI' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
      8 _ m 0#64 (BitVec.ofNat 64 (s.mem.readLE (ap + k * 8) 8)) (by simp) (by simpa using hI) ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show 8 * k + 0 % 2 ^ 64 = k * 8 by omega,
        show 8 - 0 % 2 ^ 64 = 8 by rfl]
    all_goals janus_simp
    all_goals first | rfl | (apply BitVec.eq_of_toNat_eq; simp; omega)

end FvModexp.Arm64.IntBytes
