import FvModexp.Proofs.Arm64.Nat.KSqrB

/-!
# `karatsubaSqr` (arm64): `z1.Add(z1, z0)` (natmul.go:302), `KB5 → KB6`

`kA1`: from `KB5` (`0x1bc4f4`) to the `(*Int).Add` entry (`z = x = z1`, `y = z0`), the call (`ks_intcall`) and
`KB6` from its postcondition: `z1 = X0² - (X0-X1)²` in `t` (reused, `asNeed ≤ kT`), `z`, `z2` untouched.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem spSubA (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kA1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l1 l0 l2 : Nat} (S : State)
    (hB : KB5 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk l1 l0 l2)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' ng l l2 : Nat),
      KB6 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' ng l l2 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  have hl1 := hB.hl1; have hl0 := hB.hl0; have hl2 := hB.hl2
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, -, hzh, hz48⟩ := hkm.zops
  obtain ⟨htl, htw, htg, htz, -, ht48⟩ := hkm.tops
  obtain ⟨-, hth, htacc, -⟩ := htl (by omega)
  obtain ⟨-, -, hzacc, -⟩ := hzlive (by omega)
  have hsp' : (s.sp - 320#64).toNat = s.sp.toNat - 320 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hz1 := hB.z1h; have hz0 := hB.z0h
  obtain ⟨-, e1, e2, e3⟩ := hz1
  obtain ⟨-, f1, f2, -⟩ := hz0
  have hox := hkm.iop hB.z1h (by omega) (by omega) (by omega) (by omega)
    (Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega)
    (hth.sub (Nat.le_refl _) (by omega)) hB.z1n (htw.of_sub (Nat.le_refl _) (by omega))
  have hoy := hkm.iop hB.z0h (by omega) (by omega) hzc40 (by omega)
    (Memory.accessible_sub _ hzacc (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega)
    (hzh.sub (Nat.le_refl _) (by omega)) hB.z0n (hzw.of_sub (Nat.le_refl _) (by omega))
  have hcost : IntAS.asCost l1 l0 ≤ bk := by
    refine hkm.cost (spent := kc5 (stLen s.mem st) n) ?_
    have h7 := kc7_le (ℓ := stLen s.mem st) h80
    have ha := asCost_le_asB (a := l1) (b := l0) (k := kT n) (by omega) (by omega)
    unfold kc7 kc6 at h7; omega
  unfold KGoal
  janus_run until [0x1b0910]
  refine ks_intcall impl hap R hmk hmv hwb hkm false _ ?pcS ?spS ?gS ?hm (i := 149) (by decide) ?ra
    (z := s.sp.toNat - 200) (x := s.sp.toNat - 200) (y := s.sp.toNat - 112) ?r0 ?r1 ?r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (by unfold Apart; omega)
    hox hoy (by simp only [IntAS.hC]; rw [e3]; omega) (by simp only [IntAS.hP, IntAS.hC]; rw [e1, e3]; exact htl)
    (by simp only [IntAS.hP, IntAS.hC]; rw [e1, e3]; exact htw)
    (fun _ => by
      simp only [IntAS.hP, IntAS.hC, IntAS.hL]; rw [e1, e3, f1, f2]
      exact ⟨htg, Or.inl trivial, Or.inr (by unfold Apart at htz ⊢; omega)⟩)
    (by simp only [IntAS.hL]; rw [e2, f2]; exact hcost) ?cont
  case cont =>
    intro s2 hpc2 hreg2 hk hq
    obtain ⟨-, hval, hng, hcan, hnn, hlc, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
    simp only [IntAS.hP, IntAS.hC, IntAS.hL] at hF hLF hreuse hlmax hbud
    simp only [e1, e2, e3, f2] at hF hLF hreuse hlmax hbud
    have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
    rw [intZ_of hB.z1h, intZ_of hB.z0h, hB.z1v, hB.z0v] at hval
    simp only [IntAS.resZ, IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, Bool.false_eq_true, ↓reduceIte] at hval
    simp only [IntAS.hP, IntAS.hL] at hnn
    rw [hre.1] at hval hnn
    have hs2g : s2.regs 28 = s.regs 28 := by rw [hk.2.1]; janus_simp
    rw [← hk.2.1, hs2g] at hinv
    have hF' := hF
    simp only [winA] at hF'
    rw [hsp'] at hF'
    have hzw' := hzw; have htw' := htw
    simp only [win, outside_cons, outside_nil, and_true] at hzw' htw'
    have hmin : min (max l1 l0 + 1) (kT n) ≤ kT n := Nat.min_le_right _ _
    have hrdF : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat + 48 → (x + m ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 168 ≤ x) →
        s2.mem.readLE x m = S.mem.readLE x m :=
      fun x m h1 h2 h3 => hkm.rdW (k := 4560) (a := 32) (by omega) (by omega) hF' h1 h2
        (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hrdZ : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * zc → s2.mem.readLE x m = S.mem.readLE x m := by
      intro x m h1 h2
      refine Held.readLE2 (hzh.sub h1 h2) hF hLF ?_ ?_
      · simp only [winA, outside_cons, outside_nil, and_true]; rw [hsp']; omega
      · unfold Apart at htz; simp only [outside_cons, outside_nil, and_true]; omega
    have hkm2 := (hkm.intStep (by exact hsp') (z := s.sp.toNat - 200) (q := t) (w := min (max l1 l0 + 1) (kT n))
      (Or.inl ⟨by omega, by omega⟩) (Or.inr ⟨Nat.le_refl _, by omega⟩) hF hLF hreg2 hext hbud hinv).weaken
      (spent' := kc6 (stLen s.mem st) n) (by
        have ha := asCost_le_asB (a := l1) (b := l0) (k := kT n) (by omega) (by omega)
        unfold kc6; omega)
    have hD : kD s xp n < 2 ^ (64 * kn2 n) := by
      have hX0 := natVal_lt s.mem xp (kn2 n)
      have hX1 := natVal_lt s.mem (xp + 8 * kn2 n) (n - kn2 n)
      have hpw : 2 ^ (64 * (n - kn2 n)) ≤ 2 ^ (64 * kn2 n) := Nat.pow_le_pow_right (by decide) (by omega)
      have := Nat.lt_of_lt_of_le hX1 hpw
      simp only [kD, kX0, kX1]; omega
    have hX0 : kX0 s xp n < 2 ^ (64 * kn2 n) := natVal_lt s.mem xp (kn2 n)
    have hE2 : 2 ^ (64 * kn2 n) * 2 ^ (64 * kn2 n) = 2 ^ (64 * (2 * kn2 n)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hD2 : kD s xp n * kD s xp n < 2 ^ (64 * (2 * kn2 n)) := by
      rw [← hE2]; exact Nat.mul_lt_mul'' hD hD
    have hX02 : kX0 s xp n * kX0 s xp n < 2 ^ (64 * (2 * kn2 n)) := by
      rw [← hE2]; exact Nat.mul_lt_mul'' hX0 hX0
    have hvN := natAbs_of_signed hval
    have hl : s2.mem.readLE (s.sp.toNat - 200 + 16) 8 ≤ 2 * kn2 n := natNorm_le hnn (by rw [hvN]; omega)
    refine hK s2 L' b' _ _ l2 ⟨⟨by rw [hpc2]; rfl, by rw [hk.1], hs2g, by rw [hk.2.2.1]; janus_simp,
      by rw [hk.2.2.2]; janus_simp⟩, hkm2, ⟨rfl, hre.1, rfl, hre.2⟩, hng, hcan, hl, hval, hnn,
      hB.z2h.keep fun x m h1 h2 => hrdF x m (by omega) (by omega) (Or.inr (by omega)), hl2, ?_, ?_, ?_, ?_⟩
    · rw [← hB.z2v]; unfold natVal; exact hrdZ _ _ (by omega) (by omega)
    · rcases hB.z2n with h0 | h0
      · exact Or.inl h0
      · right; rwa [hrdZ _ _ (by omega) (by omega)]
    · rw [← hB.zlo]; unfold natVal; exact hrdZ _ _ (Nat.le_refl _) (by omega)
    · rw [← hB.zhi]; unfold natVal; exact hrdZ _ _ (by omega) (by omega)
  case pcS => rfl
  case spS => exact hsp'
  case hm => rfl
  case r0 => exact spSubA _ (by omega)
  case r1 => exact spSubA _ (by omega)
  case r2 => exact spSubA _ (by omega)
  all_goals janus_simp

end FvModexp.Arm64.NatSqr
