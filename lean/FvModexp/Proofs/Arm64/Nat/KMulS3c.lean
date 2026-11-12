import FvModexp.Proofs.Arm64.Nat.KMulB
import FvModexp.Proofs.Arm64.Nat.KMulMath

set_option autoImplicit false

/-!
# `karatsuba` (arm64): `z2.mul(stk, x1, y1)` (natmul.go:214): the facts after the call → `KM5`

`kS3`: from `KM4` (`0x1bc164`) the argument setup and the inner `(*Int).mul` (`kn_icallR`: the product is written
exactly into `z[2n2:2n2 + len x1 + len y1]`, zero before), then `KM5` at the return address `0x1bc178`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le natVal_zero_part)
open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- the facts after the inner `(*Int).mul` (`kn_icallR`'s continuation) give `KM5` -/
theorem kS3post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} {S S1 s2 : State}
    (hB : KM4 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk ng l1 l0)
    (hS1 : S1.sp.toNat = s.sp.toNat - 448) (hpos : KNAt s s2 0x1bc178)
    {Lk' : List (Nat × Nat)} {bk' ng0 l' : Nat}
    (hkm2 : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk'
      (kc4 (stLen s.mem st) n + kcI (stLen s.mem st) n) s2.mem)
    (hz : IntAt s2.mem (s.sp.toNat - 208) ng0 (hP S.mem (s.sp.toNat - 208)) l' (hC S.mem (s.sp.toNat - 208)))
    (hng0 : ng0 ≤ 1) (hcan0 : ng0 = 1 → 0 < l')
    (hval : sgnV ng0 (natVal s2.mem (hP S.mem (s.sp.toNat - 208)) l') =
      intZ S.mem (s.sp.toNat - 80) * intZ S.mem (s.sp.toNat - 144))
    (hnn : NatNorm s2.mem (hP S.mem (s.sp.toNat - 208)) l')
    (hl2 : l' ≤ hL S.mem (s.sp.toNat - 80) + hL S.mem (s.sp.toNat - 144))
    (hv2 : natVal s2.mem (hP S.mem (s.sp.toNat - 208)) (hL S.mem (s.sp.toNat - 80) + hL S.mem (s.sp.toNat - 144)) =
        natVal S.mem (hP S.mem (s.sp.toNat - 80)) (hL S.mem (s.sp.toNat - 80)) *
          natVal S.mem (hP S.mem (s.sp.toNat - 144)) (hL S.mem (s.sp.toNat - 144)) ∨
      (natVal S.mem (hP S.mem (s.sp.toNat - 80)) (hL S.mem (s.sp.toNat - 80)) *
          natVal S.mem (hP S.mem (s.sp.toNat - 144)) (hL S.mem (s.sp.toNat - 144)) = 0 ∧
        natVal s2.mem (hP S.mem (s.sp.toNat - 208)) (hL S.mem (s.sp.toNat - 80) + hL S.mem (s.sp.toNat - 144)) =
          natVal S.mem (hP S.mem (s.sp.toNat - 208)) (hL S.mem (s.sp.toNat - 80) + hL S.mem (s.sp.toNat - 144))))
    (hF : MemFrame S.mem s2.mem (R.rt ++ winA S1 (W - 448) 40 ++
      [(s.sp.toNat - 208, s.sp.toNat - 208 + 32), (hP S.mem (s.sp.toNat - 208), hP S.mem (s.sp.toNat - 208) +
        8 * (hL S.mem (s.sp.toNat - 80) + hL S.mem (s.sp.toNat - 144)))] ++ stkWs S.mem st))
    (hLF : LiveFrame S.mem s2.mem Lk ([(s.sp.toNat - 208, s.sp.toNat - 208 + 32), (hP S.mem (s.sp.toNat - 208),
      hP S.mem (s.sp.toNat - 208) + 8 * (hL S.mem (s.sp.toNat - 80) + hL S.mem (s.sp.toNat - 144)))] ++
        stkWs S.mem st)) :
    KM5 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t s2 Lk' bk' ng l1 l0 l' := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hkh : kh n = (n + 1) / 2 := rfl
  have hl0 := hkm.l1; have hm0 := hkm.m1
  obtain ⟨x1, x2, x3, x4⟩ := hkm.x1h
  obtain ⟨y1, y2, y3, y4⟩ := hkm.y1h
  obtain ⟨z1, z2, z3, z4⟩ := hB.z2h
  obtain ⟨-, -, -, -, hxw, -, hzx, hxv, -⟩ := hkm.halfX (o := kh n) (l := lx1) (by omega)
  obtain ⟨-, -, -, -, hyw, -, hzy, hyv, -⟩ := hkm.halfY (o := kh n) (l := ly1) (by omega)
  simp only [hP, hC, hL, z2, z4, x2, x3, y2, y3] at hz hval hnn hl2 hF hLF hv2
  have hix : intZ S.mem (s.sp.toNat - 80) = (kX1 s xp n : Int) := by
    simp only [intZ, hNeg, hP, hL, x1, x2, x3, ↓reduceIte, hxv, hkm.v1]
  have hiy : intZ S.mem (s.sp.toNat - 144) = (kX1 s yp n : Int) := by
    simp only [intZ, hNeg, hP, hL, y1, y2, y3, ↓reduceIte, hyv, hkm.w1]
  rw [hix, hiy, ← Int.natCast_mul] at hval
  obtain ⟨e0, hv0⟩ := sgn_nonneg hval hng0 hcan0 hnn
  subst e0
  rw [hxv, hyv, hkm.v1, hkm.w1] at hv2
  have hF0 := hF
  simp only [winA, hS1] at hF
  rw [List.append_assoc] at hF
  rw [List.append_assoc] at hF0
  obtain ⟨-, htw, -, htz, -, -, -⟩ := hkm.tops
  have hts := hkm.tsep
  obtain ⟨-, -, hzw', -, hzs', -, -, hzh', -⟩ := hkm.zops
  have hstw : Outside st 24 (win s W 72) := hkm.F.stk.2.2.1
  have hfrw := hkm.stk.2.2.1
  have hslc := hkm.sok.2.2.2.2.2.1
  have hkTd : kT n = 2 * kh n + 1 := rfl
  obtain ⟨s1, s2', -⟩ := hzs'
  obtain ⟨u1, u2, -⟩ := hts
  simp only [BasicSqr.freeP, BasicSqr.freeN] at s2' u2
  unfold Apart at s1 s2' u1 u2 htz
  simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hzw' hstw hfrw htw
  have hrd : ∀ x m, s.sp.toNat - 368 ≤ x → x + m ≤ s.sp.toNat + 72 → (x + m ≤ s.sp.toNat - 208 ∨
      s.sp.toNat - 176 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 h3 => hkm.rdW (k := W - 448) (a := 40) (by omega) (by omega) hF h1 h2
      (by clear s1 s2' u1 u2 htz htw
          simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
  -- `z` and `t` outside the written part keep their bytes
  have hkz : ∀ a m, ((zp ≤ a ∧ a + m ≤ zp + 8 * zc) ∨ (t ≤ a ∧ a + m ≤ t + 8 * kT n)) →
      (a + m ≤ zp + 16 * kh n ∨ zp + 16 * kh n + 8 * (lx1 + ly1) ≤ a) →
      s2.mem.readLE a m = S.mem.readLE a m := by
    intro a m ha hq
    have hH : Held R Lk a m := by
      rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · exact hzh'.sub q1 q2
      · exact hkm.scr.held.sub q1 q2
    refine hkm.keepH (hF := hF0) (hLF := hLF) (hsp := by exact hS1) (by omega) (by omega) hH ?_ ?_
    · simp only [win, outside_cons, outside_nil, and_true]
      rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · clear u1 u2 htw htz s1 s2' hstw hfrw hq; omega
      · clear u1 u2 hzw' htz s1 s2' hstw hfrw hq; omega
    · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
      rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · clear u1 u2 htw htz hfrw hstw; omega
      · clear s1 s2' hzw' hq hfrw hstw; omega
  have hkzT : ∀ a m, t ≤ a → a + m ≤ t + 8 * kT n → s2.mem.readLE a m = S.mem.readLE a m :=
    fun a m q1 q2 => hkz a m (Or.inr ⟨q1, q2⟩) (by clear s1 s2' u1 u2 hzw' hstw hfrw htw hrd hkz; omega)
  clear hzw' hstw hfrw htw s1 s2' u1 u2 hF hF0 hLF hzx hzy hxw hyw htz
  have h0 := hB.zhi
  have hl1 := hB.hl1
  have hl0' := hB.hl0
  refine ⟨hpos, hkm2, NatSqr.IntAt.keep hB.z1h fun x m q1 q2 => hrd x m (by omega) (by omega)
    (Or.inl (by omega)), hB.hng, hB.hcan, hl1, ?_, ?_,
    NatSqr.IntAt.keep hB.z0h fun x m q1 q2 => hrd x m (by omega) (by omega) (Or.inr (by omega)), hl0', ?_, ?_,
    hz, by omega, hv0, hnn, ?_, ?_⟩
  · have e : natVal s2.mem t l1 = natVal S.mem t l1 := by
      unfold natVal; exact hkzT _ _ (Nat.le_refl _) (by omega)
    rw [e]; exact hB.z1v
  · rcases hB.z1n with q | q
    · exact Or.inl q
    · by_cases hq0 : l1 = 0
      · exact Or.inl hq0
      · right; rwa [hkzT _ _ (by omega) (by omega)]
  · have e : natVal s2.mem zp l0 = natVal S.mem zp l0 := by
      unfold natVal; exact hkz _ _ (Or.inl ⟨Nat.le_refl _, by omega⟩) (Or.inl (by omega))
    rw [e]; exact hB.z0v
  · rcases hB.z0n with q | q
    · exact Or.inl q
    · by_cases hq0 : l0 = 0
      · exact Or.inl hq0
      · right; rwa [hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inl (by omega))]
  · rw [← hB.zlo]; unfold natVal; exact hkz _ _ (Or.inl ⟨Nat.le_refl _, by omega⟩) (Or.inl (by omega))
  · refine fill_val (by omega) h0 hv2 ?_
    unfold natVal; exact hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inr (by omega))

end FvModexp.Arm64.NatMul
