import FvModexp.Proofs.Arm64.Nat.KMulI
import FvModexp.Proofs.Arm64.Nat.KMulMath

set_option autoImplicit false

/-!
# `karatsuba` (arm64): `z0.mul(stk, x0, y0)` (natmul.go:213), `KM3 → KM4`

`kS2`: from `KM3` (`0x1bc150`) the argument setup and the inner `(*Int).mul` (`kn_icallR`: the product is written
exactly into `z[0:len x0 + len y0]` of the cleared `z`), then `KM4` at the return address `0x1bc164`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le natVal_zero_part)
open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

theorem ksp_sub2 (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`KM3 → KM4`**: `z0.mul(stk, x0, y0)` (`0x1bc150 … 0x1bc160`, `kn_icallR`) -/
theorem kS2 (impl : List Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    (ih : ∀ j, IH impl R (8 * n + 2) j)
    {Lk : List (Nat × Nat)} {bk ng l1 : Nat} (S : State)
    (hB : KM3 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk ng l1)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l0 : Nat),
      KM4 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 l0 →
      KNGoal impl R b L W st zp xp n yp s S') :
    KNGoal impl R b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have hkh : kh n = (n + 1) / 2 := rfl
  have hl0 := hkm.l0; have hm0 := hkm.m0
  obtain ⟨x1, x2, x3, x4⟩ := hkm.x0h
  obtain ⟨y1, y2, y3, y4⟩ := hkm.y0h
  obtain ⟨z1, z2, z3, z4⟩ := hB.z0h
  obtain ⟨hxacc, hx48, hxH, hxc48, hxw, hxs, hzx, hxv, hxn⟩ := hkm.halfX (o := 0) (l := lx0) (by omega)
  obtain ⟨hyacc, hy48, hyH, hyc48, hyw, hys, hzy, hyv, hyn⟩ := hkm.halfY (o := 0) (l := ly0) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hxacc hx48 hxH hxc48 hxw hxs hzx hxv hxn
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hyacc hy48 hyH hyc48 hyw hys hzy hyv hyn
  obtain ⟨-, hzlive, hzw, hzg, hzs, -, -, -, -⟩ := hkm.zops
  have hsl : stLen S.mem st + 4 * (lx0 + ly0) + 64 ≤ 2 ^ 16 := by
    rw [hkm.slen]; have := hkm.F.slb; simp only [StackNat.rnd, kT]; omega
  have hops : Ops R Lk S.mem (s.regs 28).toNat (win s W 72) st (hP S.mem (s.sp.toNat - 176))
      (hC S.mem (s.sp.toNat - 176)) (hP S.mem (s.sp.toNat - 48)) (hL S.mem (s.sp.toNat - 48))
      (hC S.mem (s.sp.toNat - 48)) (hP S.mem (s.sp.toNat - 112)) (hL S.mem (s.sp.toNat - 112))
      (hC S.mem (s.sp.toNat - 112)) := by
    simp only [hP, hL, hC, x2, x3, x4, y2, y3, y4, z2, z4]
    exact ⟨⟨by omega, hxc40, by omega, fun _ => hxacc, fun _ => ⟨hxH, hxc48⟩, fun _ => ⟨hxw, hxs⟩⟩,
      ⟨by omega, hyc40, by omega, fun _ => hyacc, fun _ => ⟨hyH, hyc48⟩, fun _ => ⟨hyw, hys⟩⟩,
      ⟨hzc40, hzlive, hzw, fun _ => ⟨hzg, hzs⟩, Or.inr fun _ _ => hzx, Or.inr fun _ _ => hzy⟩, hsl⟩
  have q456 : S.mem.readLE (s.sp.toNat + 8) 8 = st := hkm.s1
  have hsacc : S.mem.accessible (s.sp.toNat - 456) 528 false = true := by
    rw [hkm.fr.accessible]
    exact Memory.accessible_sub _ hkm.F.env.2.1.2.2.2 (Or.inr rfl) (by omega) (by omega)
  have hnex := hkm.F.nex
  have hney := hkm.F.ney
  have hopsB := IntAS.Box.mk hops
  clear hops hxacc hx48 hxH hxc48 hxs hyacc hy48 hyH hyc48 hys hzlive hzg hzs hsl
  unfold KNGoal
  janus_run [q456] until [0x1b0c50]
  refine kn_icallR impl R hkm ih _ (by rfl) ?sp ?g ?hm ?l4 ?l48 ?r0 ?r1 ?r2 ?r3
    (Or.inr ⟨by omega, by omega⟩) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold Apart; omega) (by unfold Apart; omega) ?nx ?ny hopsB.h ?lx ?ly ?ru ?ne1 ?ne2 ?hq ?hsc ?K
  case hm => rfl
  case sp => simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  case g => janus_simp
  case l4 => janus_simp
  case l48 => janus_simp
  case r0 => janus_simp; exact ksp_sub2 _ (by omega)
  case r1 => janus_simp
  case r2 => janus_simp; exact ksp_sub2 _ (by omega)
  case r3 => janus_simp; exact ksp_sub2 _ (by omega)
  case nx => simp only [hNeg, x1]; decide
  case ny => simp only [hNeg, y1]; decide
  case lx => simp only [hL, x3]; exact hl0
  case ly => simp only [hL, y3]; exact hm0
  case ru => simp only [hL, hC, x3, y3, z4]; omega
  case ne1 => simp only [hP, hC, z2, z4, x2, x4]; exact hnex
  case ne2 => simp only [hP, hC, z2, z4, y2, y4]; exact hney
  case hq => simp only [hP, hL, z2, x3, y3]; left; omega
  case hsc => have := kc7_le (stLen s.mem st) n; unfold kc7 kc6 kc5 kc4 at this; omega
  case K =>
    intro s2 Lk' bk' ng0 l' hr hreg hk hkm2 hz hng0 hcan0 hval hnn hl2 hv2 hF hLF
    have hspN : (s.sp - 448#64).toNat = s.sp.toNat - 448 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [hP, hC, hL, z2, z4, x2, x3, y2, y3] at hz hval hnn hl2 hF hLF hv2
    have hix : intZ S.mem (s.sp.toNat - 48) = (kX0 s xp n : Int) := by
      simp only [intZ, hNeg, hP, hL, x1, x2, x3, ↓reduceIte, hxv, hkm.v0]
    have hiy : intZ S.mem (s.sp.toNat - 112) = (kX0 s yp n : Int) := by
      simp only [intZ, hNeg, hP, hL, y1, y2, y3, ↓reduceIte, hyv, hkm.w0]
    rw [hix, hiy, ← Int.natCast_mul] at hval
    obtain ⟨e0, hv0⟩ := sgn_nonneg hval hng0 hcan0 hnn
    subst e0
    rw [hxv, hyv, hkm.v0, hkm.w0] at hv2
    have hF0 := hF
    simp only [winA, hspN] at hF
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
    have hrd : ∀ x m, s.sp.toNat - 368 ≤ x → x + m ≤ s.sp.toNat + 72 → (x + m ≤ s.sp.toNat - 176 ∨
        s.sp.toNat - 144 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m :=
      fun x m h1 h2 h3 => hkm.rdW (k := W - 448) (a := 40) (by omega) (by omega) hF h1 h2
        (by simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
    -- `z` and `t` outside the written part keep their bytes
    have hkz : ∀ a m, ((zp ≤ a ∧ a + m ≤ zp + 8 * zc) ∨ (t ≤ a ∧ a + m ≤ t + 8 * kT n)) →
        (a + m ≤ zp ∨ zp + 8 * (lx0 + ly0) ≤ a) → s2.mem.readLE a m = S.mem.readLE a m := by
      intro a m ha hq
      have hH : Held R Lk a m := by
        rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · exact hzh'.sub q1 q2
        · exact hkm.scr.held.sub q1 q2
      refine hkm.keepH (hF := hF0) (hLF := hLF) (hsp := by exact hspN) (by omega) (by omega) hH ?_ ?_
      · simp only [win, outside_cons, outside_nil, and_true]
        rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · clear u1 u2 htw htz s1 s2' hstw hfrw hq; omega
        · clear u1 u2 hzw' htz s1 s2' hstw hfrw hq; omega
      · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
        rcases ha with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · clear u1 u2 htw htz hfrw hstw; omega
        · clear s1 s2' hzw' hq hfrw hstw; omega
    have hzz := hB.zz
    have h0 : natVal S.mem zp (2 * kh n) = 0 := by
      have := natVal_zero_part (i := 0) (k := 2 * kh n) hzz (by omega); simpa using this
    have hhi : natVal S.mem (zp + 16 * kh n) (2 * n - 2 * kh n) = 0 := by
      have := natVal_zero_part (i := 2 * kh n) (k := 2 * n - 2 * kh n) hzz (by omega)
      rw [show zp + 8 * (2 * kh n) = zp + 16 * kh n by omega] at this; exact this
    have hkzT : ∀ a m, t ≤ a → a + m ≤ t + 8 * kT n → s2.mem.readLE a m = S.mem.readLE a m :=
      fun a m q1 q2 => hkz a m (Or.inr ⟨q1, q2⟩) (by omega)
    clear hzw' hstw hfrw htw s1 s2' u1 u2 hF hF0 hLF hzx hzy hxw hyw hzw htz
    have hl1 := hB.hl1
    refine hK s2 Lk' bk' l' ⟨⟨by rw [hr]; rfl, by rw [hk.1], by rw [hk.2.1]; exact h28, by rw [hk.2.2.1]; exact h29,
      by rw [hk.2.2.2]; exact h18⟩, hkm2, NatSqr.IntAt.keep hB.z1h fun x m q1 q2 => hrd x m (by omega) (by omega)
      (Or.inl (by omega)), hB.hng, hB.hcan, hl1, ?_, ?_, hz, by omega, hv0, hnn,
      NatSqr.IntAt.keep hB.z2h fun x m q1 q2 => hrd x m (by omega) (by omega) (Or.inl (by omega)), ?_, ?_⟩
    · have e : natVal s2.mem t l1 = natVal S.mem t l1 := by
        unfold natVal; exact hkzT _ _ (Nat.le_refl _) (by omega)
      rw [e]; exact hB.z1v
    · rcases hB.z1n with q | q
      · exact Or.inl q
      · by_cases hq0 : l1 = 0
        · exact Or.inl hq0
        · right; rwa [hkzT _ _ (by omega) (by omega)]
    · refine fill_val (by omega) h0 hv2 ?_
      unfold natVal; exact hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inr (by omega))
    · rw [← hhi]; unfold natVal; exact hkz _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inr (by omega))

end FvModexp.Arm64.NatMul
