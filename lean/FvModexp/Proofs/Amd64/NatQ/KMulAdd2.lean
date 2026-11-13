import FvModexp.Proofs.Amd64.NatQ.KMulMath
import FvModexp.Proofs.Amd64.NatQ.KMulI

set_option autoImplicit false

/-!
# [amd64 port (divmc s51) of the Q-form Arm64/NatQ/KMulAdd2.lean — TIGHT COSTS] `karatsuba` (amd64): `z1.Add(z1, z2)` (natmul.go:216), `KM6 → KM7`

`kA2`: from `KM6` (`0x5f2228`) `AX = BX = &z1`, `CX = &z2` and the `CALL (*Int).Add` (`0x5f2240`, return `0x5f2245`
pushed at `RSP - 456`), `kn_intcall`, then `KM7` at the return address: `z1 = X0·Y1 + X1·Y0` (sign clear) in `t`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (IntAt natNorm_le asCost_le_asB intZ_of pushRd)

theorem ksp_subB (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem kar_z1b (X0 X1 Y0 Y1 : Nat) :
    ((X0 : Int) - (X1 : Int)) * ((Y1 : Int) - (Y0 : Int)) + ((X0 * Y0 : Nat) : Int) =
      ((X0 * Y1 + X1 * Y0 : Nat) : Int) - ((X1 * Y1 : Nat) : Int) := by
  push_cast
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  omega

theorem kar_z2 (P Q : Nat) : ((P : Int) - (Q : Int)) + (Q : Int) = (P : Int) := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kA2Call (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} {S : State}
    (hB : KM6 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk ng l1 l0)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 (IntAS.entry false)) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (h14 : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx15 : S1.xmm 15 = s.xmm 15)
    (hm : S1.mem = S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2245)
    (r0 : S1.regs 0 = BitVec.ofNat 64 ((s.regs 4).toNat - 264)) (r1 : S1.regs 3 = BitVec.ofNat 64 ((s.regs 4).toNat - 264))
    (r2 : S1.regs 1 = BitVec.ofNat 64 ((s.regs 4).toNat - 208))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l : Nat),
      KM7 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' l →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S1 := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  have hkh : kh n = (n + 1) / 2 := rfl
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hl1 := hB.hl; have hl0 := hB.hl2
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, hzh, hz48⟩ := hkm.zops
  obtain ⟨htl, htw, htg, htz, -, -, ht48⟩ := hkm.tops
  obtain ⟨-, hth, htacc, -⟩ := htl (by omega)
  obtain ⟨-, -, hzacc, -⟩ := hzlive (by omega)
  have hox := hkm.iop hB.z1h hB.hng (by omega) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega)
    (hth.sub (Nat.le_refl _) (by omega)) hB.z1n (htw.of_sub (Nat.le_refl _) (by omega))
  have hoy := hkm.iop hB.z2h (by omega) (by omega) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_sub _ hzacc (Or.inl rfl) (by omega) (by omega)) (by omega)
    (hzh.sub (by omega) (by omega)) hB.z2n (hzw.of_sub (by omega) (by omega))
  have hoxP := hkm.pushKIOp 0x5f2245 (by omega) hox
  have hoyP := hkm.pushKIOp 0x5f2245 (by omega) hoy
  rw [← hm] at hoxP hoyP
  clear hox hoy
  have hkmP := hkm.push 0x5f2245
  rw [← hm] at hkmP
  obtain ⟨htlP, htwP, -, -, -, -, -⟩ := hkmP.tops
  obtain ⟨httl, -⟩ := hkmP.ttls
  have hz1P : IntAt S1.mem ((s.regs 4).toNat - 264) ng t l1 (kT n) := by
    rw [hm]; exact IntAt.pushK hB.z1h (by omega) (by omega)
  have hz2P : IntAt S1.mem ((s.regs 4).toNat - 208) 0 (zp + 16 * kh n) l0 (zc - 2 * kh n) := by
    rw [hm]; exact IntAt.pushK hB.z2h (by omega) (by omega)
  have hiz1 := intZ_of hz1P
  have hiz2 := intZ_of hz2P
  obtain ⟨-, e1, e2, e3⟩ := hz1P
  obtain ⟨-, f1, f2, -⟩ := hz2P
  have hcs1 : kc6 n + IntAS.asCost l1 l0 ≤ KCQ n := by
    have h7 := kc7_le n
    have ha := asCost_le_asB (a := l1) (b := l0) (k := kT n) (by omega) (by omega)
    unfold kc7 at h7; omega
  have hcost : IntAS.asCost l1 l0 ≤ bk := hkm.cost hcs1
  have hzw' := hzw; have htw' := htw
  simp only [win, outside_cons, outside_nil, and_true] at hzw' htw'
  have ht1 : natVal S1.mem t l1 = natVal S.mem t l1 := by
    rw [hm]; unfold natVal; exact pushRd (by omega)
  have hz2v : natVal S1.mem (zp + 16 * kh n) l0 = natVal S.mem (zp + 16 * kh n) l0 := by
    rw [hm]; unfold natVal; exact pushRd (by omega)
  have hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f1da0 + 1189 := by
    rw [hm, hsp, Janus.Arm64.Memory.readLE_writeLE_self]
  refine kn_intcall impl hap R hmk hmv hwb hkmP false S1 hpc hsp h14 rfl hfs (i := 1189) (by decide) hrd
    (hx15.trans hx150) (hdf.trans hdf0) r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (by unfold Apart; omega)
    hoxP hoyP (by simp only [IntAS.hC]; rw [e3]; omega) (by simp only [IntAS.hP, IntAS.hC]; rw [e1, e3]; exact htlP)
    (by simp only [IntAS.hP, IntAS.hC]; rw [e1, e3]; exact htwP)
    (fun _ => by
      simp only [IntAS.hP, IntAS.hC, IntAS.hL]; rw [e1, e3, f1, f2]
      exact ⟨htg, httl, Or.inl trivial, Or.inr (by unfold Apart at htz ⊢; omega)⟩)
    (by simp only [IntAS.hL]; rw [e2, f2]; exact hcost) ?_
  intro s2 hpc2 hreg2 hk hq
  obtain ⟨efs, edf, -, hval, hng, hcan, hnn, hlc, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
  simp only [IntAS.hP, IntAS.hC, IntAS.hL] at hF hLF hreuse hlmax hbud
  simp only [e1, e2, e3, f2] at hF hLF hreuse hlmax hbud
  have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
  rw [hiz1, hiz2] at hval
  simp only [↓reduceIte] at hval
  rw [ht1, hz2v] at hval
  have hz1v := hB.z1v
  rw [kar_z1b] at hz1v
  unfold sgnV at hz1v
  rw [hz1v, hB.z2v] at hval
  simp only [IntAS.resZ, Bool.false_eq_true, ↓reduceIte] at hval
  rw [kar_z2] at hval
  simp only [IntAS.hP, IntAS.hL] at hnn
  rw [hre.1] at hnn
  have hval' : sgnV (IntAS.hNeg s2.mem ((s.regs 4).toNat - 264))
      (natVal s2.mem t (IntAS.hL s2.mem ((s.regs 4).toNat - 264))) =
      ((kX0 s xp n * kX1 s yp n + kX1 s xp n * kX0 s yp n : Nat) : Int) := by
    rw [← hval]; simp only [IntAS.intZ, sgnV, IntAS.hNeg, IntAS.hP, IntAS.hL, hre.1]
  obtain ⟨hng0, hv⟩ := sgn_nonneg hval' hng hcan hnn
  simp only [IntAS.hL, IntAS.hC] at hlc
  rw [hre.2] at hlc
  rw [h14] at hinv
  have hF' := hF
  simp only [win, hsp] at hF'
  have hrdZ : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * zc → s2.mem.readLE x m = S.mem.readLE x m := by
    intro x m h1 h2
    refine (Held.readLE2 (hzh.sub h1 h2) hF hLF ?_ ?_).trans (by rw [hm]; exact pushRd (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
    · unfold Apart at htz; simp only [outside_cons, outside_nil, and_true]; omega
  have hkm2 := (hkmP.intStep hsp (z := (s.regs 4).toNat - 264) (q := t) (w := min (max l1 l0 + 1) (kT n))
    (Or.inl ⟨by omega, by omega⟩) (Or.inr ⟨Nat.le_refl _, by omega⟩) hF hLF hreg2 hext hbud hcs1 hinv).weaken
    (spent' := kc7 n) (by
      have ha := asCost_le_asB (a := l1) (b := l0) (k := kT n) (by omega) (by omega)
      unfold kc7; omega) (by have h7 := kc7_le n; omega)
  refine hK s2 L' b' _ ⟨⟨by rw [hpc2], by rw [hk.1]; exact sp_add8K hsp (by omega), hk.2.2.1.trans h14,
    hk.2.1.trans h5, efs.trans hfs, edf.trans hdf, hk.2.2.2.trans hx15⟩, hkm2,
    ⟨hng0, hre.1, rfl, hre.2⟩, hlc, hv, ?_, ?_⟩
  · rw [← hB.zlo]; unfold natVal; exact hrdZ _ _ (Nat.le_refl _) (by omega)
  · rw [← hB.zhi]; unfold natVal; exact hrdZ _ _ (by omega) (by omega)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`KM6 → KM7`**: `AX = BX = &z1`, `CX = &z2` and the `CALL (*Int).Add` (`0x5f2228 … 0x5f2240`), then `kA2Call` -/
theorem kA2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hB : KM6 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk ng l1 l0)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l : Nat),
      KM7 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' l →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  obtain ⟨hW, hWs, hal, ha48, -⟩ := hB.km.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := hB.km.F.env.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hB.km.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KNGoal
  janus64_run [hsp'] until [0x5e2620]
  refine kA2Call impl hap R hmk hmv hwb hB hx150 hdf0 _ (by rfl) ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ hK
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega | exact ksp_subB _ (by omega)

end FvModexp.Amd64.Q.NatMul
