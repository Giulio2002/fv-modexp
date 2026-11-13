import FvModexp.Proofs.Arm64.NatQ.KMulI
import FvModexp.Proofs.Arm64.NatQ.KMulS3c

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/KMulS3.lean — TIGHT COSTS, divmc s34] `karatsuba` (arm64): `z2.mul(stk, x1, y1)` (natmul.go:214), `KM4 → KM5`

`kS3`: from `KM4` (`0x1bc164`) the argument setup and the inner `(*Int).mul` (`kn_icallR`: the product is written
exactly into `z[2n2:2n2 + len x1 + len y1]`, zero before), then `KM5` at the return address `0x1bc178`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le natVal_zero_part)
open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

theorem ksp_sub3 (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`KM4 → KM5`**: `z2.mul(stk, x1, y1)` (`0x1bc164 … 0x1bc174`, `kn_icallR`) -/
theorem kS3 (impl : List Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    (ih : ∀ j, IH impl R H (8 * n + 2) j)
    {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} (S : State)
    (hB : KM4 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk ng l1 l0)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l2 : Nat),
      KM5 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 l0 l2 →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have hkh : kh n = (n + 1) / 2 := rfl
  have hl0 := hkm.l1; have hm0 := hkm.m1
  obtain ⟨x1, x2, x3, x4⟩ := hkm.x1h
  obtain ⟨y1, y2, y3, y4⟩ := hkm.y1h
  obtain ⟨z1, z2, z3, z4⟩ := hB.z2h
  obtain ⟨hxacc, hx48, hxH, hxc48, hxw, hxs, hzx, hxv, hxn⟩ := hkm.halfX (o := kh n) (l := lx1) (by omega)
  obtain ⟨hyacc, hy48, hyH, hyc48, hyw, hys, hzy, hyv, hyn⟩ := hkm.halfY (o := kh n) (l := ly1) (by omega)
  obtain ⟨-, -, -, -, -, -, hzlive, hzw, hzg, hzs⟩ := hkm.partZ (o := 2 * kh n) (l := 2 * n - 2 * kh n) (by omega)
  rw [show zp + 8 * (2 * kh n) = zp + 16 * kh n by omega] at hzlive hzw hzg hzs
  have hzx0 := hkm.F.zx
  have hzy0 := hkm.F.zy
  have hsl : stLen S.mem st + 4 * (lx1 + ly1) + 64 ≤ 2 ^ 16 := by
    rw [hkm.slen]; have := hkm.F.slb; simp only [StackNat.rnd, kT]; omega
  have hops : Ops R Lk S.mem (s.regs 28).toNat (win s W 72) st (hP S.mem (s.sp.toNat - 208))
      (hC S.mem (s.sp.toNat - 208)) (hP S.mem (s.sp.toNat - 80)) (hL S.mem (s.sp.toNat - 80))
      (hC S.mem (s.sp.toNat - 80)) (hP S.mem (s.sp.toNat - 144)) (hL S.mem (s.sp.toNat - 144))
      (hC S.mem (s.sp.toNat - 144)) := by
    simp only [hP, hL, hC, x2, x3, x4, y2, y3, y4, z2, z4]
    exact ⟨⟨by omega, by omega, by omega, fun _ => hxacc, fun _ => ⟨hxH, hxc48⟩, fun _ => ⟨hxw, hxs⟩⟩,
      ⟨by omega, by omega, by omega, fun _ => hyacc, fun _ => ⟨hyH, hyc48⟩, fun _ => ⟨hyw, hys⟩⟩,
      ⟨by omega, hzlive, hzw, fun _ => ⟨hzg, hzs⟩, Or.inr fun _ _ => by unfold Apart at hzx0 ⊢; omega,
        Or.inr fun _ _ => by unfold Apart at hzy0 ⊢; omega⟩, hsl⟩
  have q456 : S.mem.readLE (s.sp.toNat + 8) 8 = st := hkm.s1
  have hsacc : S.mem.accessible (s.sp.toNat - 456) 528 false = true := by
    rw [hkm.fr.accessible]
    exact Memory.accessible_sub _ hkm.F.env.2.1.2.2.2 (Or.inr rfl) (by omega) (by omega)
  have hnex := hkm.F.nex
  have hney := hkm.F.ney
  have hopsB := IntAS.Box.mk hops
  clear hops hxacc hx48 hxH hxc48 hxs hyacc hy48 hyH hyc48 hys hzlive hzg hzs hsl hzx0 hzy0
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
  case r0 => janus_simp; exact ksp_sub3 _ (by omega)
  case r1 => janus_simp
  case r2 => janus_simp; exact ksp_sub3 _ (by omega)
  case r3 => janus_simp; exact ksp_sub3 _ (by omega)
  case nx => simp only [hNeg, x1]; decide
  case ny => simp only [hNeg, y1]; decide
  case lx => simp only [hL, x3]; omega
  case ly => simp only [hL, y3]; omega
  case ru => simp only [hL, hC, x3, y3, z4]; omega
  case ne1 => simp only [hP, hC, z2, z4, x2, x4]; omega
  case ne2 => simp only [hP, hC, z2, z4, y2, y4]; omega
  case hq => simp only [hP, hL, z2, x3, y3]; left; omega
  case hsc => have := kc7_le n; unfold kc7 kc6 kc5 at this; omega
  case K =>
    intro s2 Lk' bk' ng0 l' hr hreg hk hkm2 hz hng0 hcan0 hval hnn hl2 hv2 hF hLF
    exact hK s2 Lk' bk' l' (kS3post hB (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
      ⟨by rw [hr]; rfl, by rw [hk.1], by rw [hk.2.1]; exact h28, by rw [hk.2.2.1]; exact h29,
        by rw [hk.2.2.2]; exact h18⟩ hkm2 hz hng0 hcan0 hval hnn hl2 hv2 hF hLF)

end FvModexp.Arm64.Q.NatMul
