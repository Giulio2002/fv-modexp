import FvModexp.Proofs.Amd64.Int.IntBytesDefs

/-! # `(*Int).Bytes` (amd64): the zero-skip loop (`+0x95`) and the return `buf[i:]` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface
open FvModexp

namespace FvModexp.Amd64.IntBytes

/-- The postcondition from the loop facts at the return. -/
theorem post_intro {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {x : BitVec 64} {s : State} {ret q ap N : Nat}
    {L' : List (Nat × Nat)} {b' : Nat} {m : Janus.Arm64.Memory} (hI : Inv R b L x s ret q ap N N L' b' m)
    (hap : ap = s.mem.readLE (x.toNat + 8) 8) (hN : N = 8 * s.mem.readLE (x.toNat + 16) 8)
    (s' : State) (i p n : Nat) (hfs : s'.fsBase = s.fsBase) (hm : s'.mem = m) (h0 : (s'.regs 0).toNat = p)
    (h1 : (s'.regs 3).toNat = n) (h2 : (s'.regs 1).toNat = n) (hz : ∀ j, j < i → (m.bytes (q + j)).toNat = 0) (hi : i ≤ N)
    (hcase : (i = N ∧ p = q ∧ n = 0) ∨ (i < N ∧ p = q + i ∧ n = N - i ∧ (m.bytes (q + i)).toNat ≠ 0)) :
    Post R b L x s s' := by
  obtain ⟨-, -, -, hN0, hq48, hqacc, -, -, hqL, hqR, hqA, hw, hext, hb', hinv, hfr, hlf⟩ := hI
  subst hm
  have hval : IntV s.mem x.toNat = s.mem.readLE ap N := by simp only [IntV, natVal, hap, hN]
  have hrev : beVal s'.mem q N = s.mem.readLE ap N := beVal_rev hw
  have hlen : N / 8 = lenW s.mem x.toNat := by simp only [lenW, hN]; omega
  rw [hlen] at hb'
  refine ⟨hfs, p, n, n, h0, h1, h2, Nat.le_refl _, ?_, ?_, L', b', hext, hb', hinv, ?_, hfr, hlf⟩
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
        Janus.Arm64.Memory.accessible_mono _ hqacc (by omega) (by omega), by omega⟩
      have := hqA r hr; unfold Apart at this ⊢; omega

/-- `MOVZX` + `TESTB`: the loaded byte as the executor leaves it. -/
theorem byte8_toNat (v : Nat) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v)))).toNat = v % 256 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem byte8_zero {v : Nat} (h : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v))) = 0#8) :
    v % 256 = 0 := by
  have := congrArg BitVec.toNat h; rw [byte8_toNat] at this; simpa using this

theorem byte8_ne {v : Nat} (h : ¬BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v))) = 0#8) :
    v % 256 ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [byte8_toNat, h']; rfl))

/-- Go's slice-pointer mask on amd64 (`NEGQ; SARQ $63; ANDQ`): `i` when `0 < len - i`. -/
theorem mask_lt (I X : BitVec 64) (h0 : 0 < X.toNat) (h1 : X.toNat < 2 ^ 63) : I &&& (0#64 - X).sshiftRight 63 = I := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  exact sliceMask_lt _ 0#64 X (by simpa using h0) h1 I.isLt

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- The zero-skip loop `for i < len(buf) && buf[i] == 0 { i++ }` and the return of `buf[i:]`. -/
theorem skipLoop (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)
    (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [fn]).link impl) ret) (s : State)
    (q ap N : Nat) (L' : List (Nat × Nat)) (b' : Nat) (m : Janus.Arm64.Memory)
    (hI : Inv R b L x s ret q ap N N L' b' m)
    (hap : ap = s.mem.readLE (x.toNat + 8) 8) (hN : N = 8 * s.mem.readLE (x.toNat + 16) 8) (hN1 : N ≤ 1024)
    (hsp : 4160 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 16 ≤ 2 ^ 48 ∧ (s.regs 4).toNat % 8 = 0)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4160) (4160 + 16) true = true) :
    ∀ k (S : State) (I : BitVec 64), I.toNat + k = N → (∀ j, j < I.toNat → (m.bytes (q + j)).toNat = 0) →
      S.rip = BitVec.ofNat 64 hSkip → S.regs 4 = s.regs 4 - 40#64 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 N → S.regs 7 = I →
      S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.mem = m →
      Reaches (((Extracted.program.onlySegments [fn]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L x s s') := by
  have hI' := hI
  obtain ⟨hm1, hm2, -, hN0, hq48, hqacc, -, -, -, -, -, -, -, -, -, hfr, -⟩ := hI'
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  intro k
  induction k with
  | zero =>
    intro S I hI0 hz hpc hsp hr0 hr1 hr7 hr14 hx15 hfs hm
    have hIN : I = BitVec.ofNat 64 N := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hIN
    have hq0 : (BitVec.ofNat 64 q).toNat = q := by simp; omega
    janus64_run [hm1, hm2, BitVec.msb_eq_decide]
    have hzN : ∀ j, j < N → (m.bytes (q + j)).toNat = 0 := fun j hj => hz j (by simp; omega)
    refine post_intro hI hap hN _ N q 0 hfs rfl ?_ ?_ ?_ hzN (Nat.le_refl _) (Or.inl ⟨rfl, rfl, rfl⟩)
    all_goals janus64_simp
    all_goals omega
  | succ k ih =>
    intro S I hI0 hz hpc hsp hr0 hr1 hr7 hr14 hx15 hfs hm
    have hX0 : 0 < (BitVec.ofNat 64 N - I).toNat := by rw [BitVec.toNat_sub]; simp; omega
    have hX1 : (BitVec.ofNat 64 N - I).toNat = N - I.toNat := by rw [BitVec.toNat_sub]; simp; omega
    have hmk := mask_lt I (BitVec.ofNat 64 N - I) hX0 (by omega)
    janus64_run [hm1, hm2, BitVec.msb_eq_decide] until [hSkip]
    · refine ih _ (I + 1#64) (by janus64_simp; omega) (fun j hj => ?_) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) hfs
        (by janus64_simp)
      have h := byte8_zero (by janus_assumption :
        BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE (q + I.toNat) 1)))) = 0#8)
      have hj' : j < I.toNat + 1 := by
        have : (I + 1#64).toNat = I.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
        omega
      by_cases hjI : j = I.toNat
      · subst hjI; rw [Janus.Arm64.Memory.readLE_one] at h; have := (m.bytes (q + I.toNat)).isLt; omega
      · exact hz j (by omega)
    · have h := byte8_ne (by janus_assumption :
        ¬BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (m.readLE (q + I.toNat) 1)))) = 0#8)
      rw [Janus.Arm64.Memory.readLE_one] at h
      have hb := (m.bytes (q + I.toNat)).isLt
      refine post_intro hI hap hN _ I.toNat (q + I.toNat) (N - I.toNat) hfs rfl ?_ ?_ ?_ hz (by omega)
        (Or.inr ⟨by omega, rfl, rfl, by omega⟩)
      all_goals janus64_simp
      all_goals first
        | omega
        | (rw [sliceMask_lt _ 0#64 _ (by simpa using hX0) (by omega) I.isLt]; omega)

end FvModexp.Amd64.IntBytes
