import FvModexp.Proofs.Arm64.Int.IntBytesDefs

/-! # `(*Int).Bytes` (arm64): the zero-skip loop (`+0xb4`) and the return `buf[i:]` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.IntBytes

/-- The postcondition from the loop facts at the return. -/
theorem post_intro {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {x : BitVec 64} {s : State} {ret q ap N : Nat}
    {L' : List (Nat × Nat)} {b' : Nat} {m : Memory} (hI : Inv R b L x s ret q ap N N L' b' m)
    (hap : ap = s.mem.readLE (x.toNat + 8) 8) (hN : N = 8 * s.mem.readLE (x.toNat + 16) 8)
    (s' : State) (i p n : Nat) (hm : s'.mem = m) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 1).toNat = n)
    (h2 : (s'.regs 2).toNat = n) (hz : ∀ j, j < i → (m.bytes (q + j)).toNat = 0) (hi : i ≤ N)
    (hcase : (i = N ∧ p = q ∧ n = 0) ∨ (i < N ∧ p = q + i ∧ n = N - i ∧ (m.bytes (q + i)).toNat ≠ 0)) :
    Post R b L x s s' := by
  obtain ⟨-, -, -, hN0, hq48, hqacc, -, -, hqL, hqR, hqA, hw, hext, hb', hinv, hfr, hlf⟩ := hI
  subst hm
  have hval : IntV s.mem x.toNat = s.mem.readLE ap N := by simp only [IntV, natVal, hap, hN]
  have hrev : beVal s'.mem q N = s.mem.readLE ap N := beVal_rev hw
  have hlen : N / 8 = lenW s.mem x.toNat := by simp only [lenW, hN]; omega
  rw [hlen] at hb'
  refine ⟨p, n, n, h0, h1, h2, Nat.le_refl _, ?_, ?_, L', b', hext, hb', hinv, ?_, hfr, hlf⟩
  · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hiN, rfl, rfl, -⟩
    · have := beVal_skip (n := 0) hz
      rw [Nat.add_zero, hrev, beVal_zero] at this
      rw [hval, this]; rfl
    · rw [← beVal_skip hz, show i + (N - i) = N by omega, hrev, hval]
  · rcases hcase with ⟨-, -, rfl⟩ | ⟨-, rfl, -, hnz⟩
    · exact Or.inl rfl
    · exact Or.inr hnz
  · intro hn
    rcases hcase with ⟨-, -, rfl⟩ | ⟨hiN, rfl, rfl, -⟩
    · omega
    · refine ⟨hqL.sub (by omega) (by omega), hqR.sub (by omega) (by omega), fun r hr => ?_,
        Memory.accessible_mono _ hqacc (by omega) (by omega), by omega⟩
      have := hqA r hr; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- The zero-skip loop `for i < len(buf) && buf[i] == 0 { i++ }` and the return of `buf[i:]`. -/
theorem skipLoop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (q ap N : Nat) (L' : List (Nat × Nat)) (b' : Nat) (m : Memory)
    (hI : Inv R b L x s ret q ap N N L' b' m)
    (hap : ap = s.mem.readLE (x.toNat + 8) 8) (hN : N = 8 * s.mem.readLE (x.toNat + 16) 8) (hN1 : N ≤ 1024)
    (hsp : 4160 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4160) (4160 + 16) true = true) :
    ∀ k (S : State) (I : BitVec 64), I.toNat + k = N → (∀ j, j < I.toNat → (m.bytes (q + j)).toNat = 0) →
      S.pc = BitVec.ofNat 64 hSkip → S.sp = s.sp - 64#64 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 N → S.regs 5 = BitVec.ofNat 64 (N / 8) → S.regs 6 = I →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L x s s') := by
  have hI' := hI
  obtain ⟨hm1, hm2, -, hN0, hq48, hqacc, -, -, -, -, -, -, -, -, -, hfr, -⟩ := hI'
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  have h8 : (N / 8) <<< 3 = N := by rw [Nat.shiftLeft_eq]; omega
  have h88 : N / 8 * 8 = N := by omega
  intro k
  induction k with
  | zero =>
    intro S I hI0 hz hpc hsp hr0 hr1 hr5 hr6 hr28 hr18 hm
    janus_run [hm1, hm2, h88]
    have hzN : ∀ j, j < N → (m.bytes (q + j)).toNat = 0 := fun j hj => hz j (by omega)
    all_goals refine post_intro hI hap hN _ N q 0 ?_ ?_ ?_ ?_ hzN (Nat.le_refl _) (Or.inl ⟨rfl, rfl, rfl⟩)
    all_goals janus_simp
    all_goals first
      | rfl
      | omega
      | (rw [show I = BitVec.ofNat 64 N from BitVec.eq_of_toNat_eq (by simp; omega), sliceMask_eq]; omega)
  | succ k ih =>
    intro S I hI0 hz hpc hsp hr0 hr1 hr5 hr6 hr28 hr18 hm
    janus_run [hm1, hm2, h88] until [hSkip]
    · refine ih _ (I + 1#64) (by janus_simp; omega) (fun j hj => ?_) (by janus_simp) (by janus_simp) (by janus_simp)
        (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
      have h := (by janus_assumption : m.readLE (q + I.toNat) 1 % 4294967296 = 0)
      have hj' : j < I.toNat + 1 := by
        have : (I + 1#64).toNat = I.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
        omega
      by_cases hjI : j = I.toNat
      · subst hjI; rw [Memory.readLE_one] at h; omega
      · exact hz j (by omega)
    · have h := (by janus_assumption : ¬m.readLE (q + I.toNat) 1 % 4294967296 = 0)
      rw [Memory.readLE_one] at h
      refine post_intro hI hap hN _ I.toNat (q + I.toNat) (N - I.toNat) ?_ ?_ ?_ ?_ hz (by omega)
        (Or.inr ⟨by omega, rfl, rfl, by omega⟩)
      all_goals janus_simp
      all_goals first
        | rfl
        | omega
        | (rw [sliceMask_lt _ _ _ (by simp; omega) (by simp; omega) I.isLt]; omega)

end FvModexp.Arm64.IntBytes
