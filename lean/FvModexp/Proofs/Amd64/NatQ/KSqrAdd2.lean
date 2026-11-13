import FvModexp.Proofs.Amd64.NatQ.KSqrB

/-!
# [amd64 port (divmc s39) of the Q-form Arm64/NatQ/KSqrAdd2.lean — TIGHT COSTS] `karatsubaSqr` (amd64): `z1.Add(z1, z2)` (natmul.go:303), `KB6 → KB7`

`kA2Call`: at the `(*Int).Add` entry (`z = x = z1`, `y = z2`; return `0x5f271d` pushed at `SP - 320`), the call
(`ks_intcall`) and `KB7` from its postcondition: `z1 = 2·X0·X1` (sign clear, `ks_z1`, `int_nonneg_abs`) in `t`,
`z` untouched. `kA2`: from `KB6` (`0x5f2708`) to the call.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

theorem spSubB (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kA2Call (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} {S : State}
    (hB : KB6 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk ng l1 l0)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 (IntAS.entry false)) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 320)
    (h14 : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx15 : S1.xmm 15 = s.xmm 15)
    (hm : S1.mem = S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f271d)
    (r0 : S1.regs 0 = BitVec.ofNat 64 ((s.regs 4).toNat - 200)) (r1 : S1.regs 3 = BitVec.ofNat 64 ((s.regs 4).toNat - 200))
    (r2 : S1.regs 1 = BitVec.ofNat 64 ((s.regs 4).toNat - 144))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l : Nat),
      KB7 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S1 := by
  have hkmS := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkmS.lay
  have hkm := hkmS.push 0x5f271d
  rw [← hm] at hkm
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  have hl1 := hB.hl; have hl0 := hB.hl2
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, -, hzh, hz48⟩ := hkm.zops
  obtain ⟨htl, htw, htg, htz, -, ht48⟩ := hkm.tops
  obtain ⟨htt, hzt⟩ := hkm.ttls
  obtain ⟨-, hth, htacc, -⟩ := htl (by omega)
  obtain ⟨-, -, hzacc, -⟩ := hzlive (by omega)
  have hzw' := hzw; have htw' := htw
  simp only [win, outside_cons, outside_nil, and_true] at hzw' htw'
  -- reads through the push
  have hpr : ∀ x m, (x + m ≤ (s.regs 4).toNat - 320 ∨ (s.regs 4).toNat - 312 ≤ x) →
      S1.mem.readLE x m = S.mem.readLE x m := fun x m h => by rw [hm]; exact pushRd (by omega)
  have hz1 : IntAt S1.mem ((s.regs 4).toNat - 200) ng t l1 (kT n) := by rw [hm]; exact hB.z1h.push (by omega) (by omega)
  have hz0 : IntAt S1.mem ((s.regs 4).toNat - 144) 0 (zp + 16 * kn2 n) l0 (zc - 2 * kn2 n) := by
    rw [hm]; exact hB.z2h.push (by omega) (by omega)
  have hz1v : (if ng = 0 then (natVal S1.mem t l1 : Int) else -(natVal S1.mem t l1 : Int)) =
      -((kD s xp n * kD s xp n : Nat) : Int) + ((kX0 s xp n * kX0 s xp n : Nat) : Int) := by
    rw [← hB.z1v]; unfold natVal; rw [hpr _ _ (by omega)]
  have hz0v : natVal S1.mem (zp + 16 * kn2 n) l0 = kX1 s xp n * kX1 s xp n := by
    rw [← hB.z2v]; unfold natVal; exact hpr _ _ (by omega)
  have hz1n : NatNorm S1.mem t l1 := by
    rcases hB.z1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hpr _ _ (by omega)]
  have hz0n : NatNorm S1.mem (zp + 16 * kn2 n) l0 := by
    rcases hB.z2n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hpr _ _ (by omega)]
  have hz1c := hz1; have hz0c := hz0
  obtain ⟨-, e1, e2, e3⟩ := hz1c
  obtain ⟨-, f1, f2, -⟩ := hz0c
  have hox := hkm.iop hz1 hB.hng (by omega) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega)
    (hth.sub (Nat.le_refl _) (by omega)) hz1n (htw.of_sub (Nat.le_refl _) (by omega))
  have hoy := hkm.iop hz0 (by omega) (by omega) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_sub _ hzacc (Or.inl rfl) (by omega) (by omega)) (by omega)
    (hzh.sub (by omega) (by omega)) hz0n (hzw.of_sub (by omega) (by omega))
  have hcs : kc6 n + IntAS.asCost l1 l0 ≤ ksqrCQ n := by
    have h7 := kc7_le h80
    have ha := asCost_le_asB (a := l1) (b := l0) (k := kT n) (by omega) (by omega)
    unfold kc7 at h7; omega
  have hcost : IntAS.asCost l1 l0 ≤ bk := hkm.cost hcs
  have hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f2380 + 925 := by
    rw [hm, hsp, Janus.Arm64.Memory.readLE_writeLE_self]
  refine ks_intcall impl hap R hmk hmv hwb hkm false S1 hpc hsp h14 rfl hfs (i := 925) (by decide) hrd
    (hx15.trans hx150) (hdf.trans hdf0)
    (z := (s.regs 4).toNat - 200) (x := (s.regs 4).toNat - 200) (y := (s.regs 4).toNat - 144) r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (by unfold Apart; omega)
    hox hoy (by simp only [IntAS.hC]; rw [e3]; omega) (by simp only [IntAS.hP, IntAS.hC]; rw [e1, e3]; exact htl)
    (by simp only [IntAS.hP, IntAS.hC]; rw [e1, e3]; exact htw)
    (fun _ => by
      simp only [IntAS.hP, IntAS.hC, IntAS.hL]; rw [e1, e3, f1, f2]
      exact ⟨htg, htt, Or.inl trivial, Or.inr (by unfold Apart at htz ⊢; omega)⟩)
    (by simp only [IntAS.hL]; rw [e2, f2]; exact hcost) ?cont
  case cont =>
    intro s2 hpc2 hreg2 hk hq
    obtain ⟨efs, edf, -, hval, hng, hcan, hnn, hlc, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
    simp only [IntAS.hP, IntAS.hC, IntAS.hL] at hF hLF hreuse hlmax hbud
    simp only [e1, e2, e3, f2] at hF hLF hreuse hlmax hbud
    have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
    rw [intZ_of hz1, hz1v, intZ_of hz0] at hval
    simp only [↓reduceIte] at hval
    rw [hz0v] at hval
    simp only [IntAS.resZ, IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, Bool.false_eq_true, ↓reduceIte] at hval
    simp only [IntAS.hP, IntAS.hL] at hnn
    rw [hre.1] at hval hnn
    rw [h14] at hinv
    have hF' := hF
    simp only [win, hsp] at hF'
    have hmin : min (max l1 l0 + 1) (kT n) ≤ kT n := Nat.min_le_right _ _
    have hrdF : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat + 48 →
        (x + m ≤ (s.regs 4).toNat - 200 ∨ (s.regs 4).toNat - 168 ≤ x) →
        s2.mem.readLE x m = S.mem.readLE x m :=
      fun x m h1 h2 h3 => (hkm.rdW (k := 4536) (a := 32) (by omega) (by omega) hF' h1 h2
        (by simp only [outside_cons, outside_nil, and_true]; omega)).trans (hpr x m (by omega))
    have hrdZ : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * zc → s2.mem.readLE x m = S.mem.readLE x m := by
      intro x m h1 h2
      refine (Held.readLE2 (hzh.sub h1 h2) hF hLF ?_ ?_).trans (hpr x m (by omega))
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · unfold Apart at htz; simp only [outside_cons, outside_nil, and_true]; omega
    have hkm2 := (hkm.intStep hsp (z := (s.regs 4).toNat - 200) (q := t) (w := min (max l1 l0 + 1) (kT n))
      (Or.inl ⟨by omega, by omega⟩) (Or.inr ⟨Nat.le_refl _, by omega⟩) hF hLF hreg2 hext hbud hcs hinv).weaken
      (spent' := kc7 n) (by
        have ha := asCost_le_asB (a := l1) (b := l0) (k := kT n) (by omega) (by omega)
        unfold kc7; omega) (by have h7 := kc7_le h80; omega)
    have hz : -((kD s xp n * kD s xp n : Nat) : Int) + ((kX0 s xp n * kX0 s xp n : Nat) : Int) +
        ((kX1 s xp n * kX1 s xp n : Nat) : Int) = ((2 * kX0 s xp n * kX1 s xp n : Nat) : Int) := ks_z1 _ _
    rw [hz] at hval
    have hng0 : s2.mem.readLE ((s.regs 4).toNat - 200) 1 = 0 := by
      rcases Nat.eq_zero_or_pos (s2.mem.readLE ((s.regs 4).toNat - 200) 1) with h0 | h0
      · exact h0
      · exfalso
        have h1 : s2.mem.readLE ((s.regs 4).toNat - 200) 1 = 1 := by simp only [IntAS.hNeg] at hng; omega
        have hpos := hcan (by simp only [IntAS.hNeg]; exact h1)
        simp only [IntAS.hL] at hpos
        have hlow := SubMod2N.natVal_lower s2.mem t _ hnn hpos
        have h1p := Nat.one_le_two_pow (n := 64 * (s2.mem.readLE ((s.regs 4).toNat - 200 + 16) 8 - 1))
        rw [if_neg (by omega)] at hval
        omega
    have hv := int_nonneg_abs hval (by simp only [IntAS.hNeg] at hng; exact hng)
      (fun h => absurd h (by rw [hng0]; omega))
    simp only [IntAS.hL, IntAS.hC] at hlc
    rw [hre.2] at hlc
    refine hK s2 L' b' _ ⟨⟨by rw [hpc2], by rw [hk.1]; exact sp_add8 hsp (by omega), hk.2.2.1.trans h14,
      hk.2.1.trans h5, efs.trans hfs, edf.trans hdf, hk.2.2.2.trans hx15⟩, hkm2, ⟨hng0, hre.1, rfl, hre.2⟩, hlc, hv, ?_, ?_⟩
    · rw [← hB.zlo]; unfold natVal; exact hrdZ _ _ (Nat.le_refl _) (by omega)
    · rw [← hB.zhi]; unfold natVal; exact hrdZ _ _ (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB6 → KB7`**: the loads and the `CALL (*Int).Add` (`0x5f2708 … 0x5f2718`), then `kA2Call` -/
theorem kA2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk ng l1 l0 : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hB : KB6 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk ng l1 l0)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l : Nat),
      KB7 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KGoal
  janus64_run [hsp'] until [0x5e2620]
  refine kA2Call impl hap R hmk hmv hwb hB hx150 hdf0 _ (by rfl) ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ hK
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega | exact spSubB _ (by omega)

end FvModexp.Amd64.Q.NatSqr
