import FvModexp.Proofs.Amd64.Exp.EvSetT
import FvModexp.Proofs.Amd64.Exp.EvSetR

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `setJ` → `mvJ` (asm s61; twin of infra's arm64 `EvSetU`)

`jo_own` (`JS` through `runJ`'s spills of `z` and the `CALL`'s push), `setTl` (`JS → J9`: `runJ`; same pointer →
`J9` directly; else `memmove(pZ, pw, 8·lw)` (`mvCall`, also for `lw = 0`), `JO.mv`, `runMv`, the copied value).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

theorem cp_sub {m0 m : Memory} {d s n j k : Nat} (h : Mem.Copied m0 m d s n) (hj : j + k ≤ n) :
    Mem.Copied m0 m (d + j) (s + j) k := fun i hi => by
  have := h (j + i) (by omega)
  rw [← Nat.add_assoc, ← Nat.add_assoc] at this
  exact this

/-- the frame written by `runJ` (both paths) -/
@[reducible] def FJ (sp : Nat) : List (Nat × Nat) := [(sp - 8, sp), (sp + 0xa0, sp + 0xb0), (sp + 0x108, sp + 0x110)]

theorem fr_KE {sp : Nat} {M M' : Memory} (hsp : 8 ≤ sp)
    (h : MemFrame M M' [(sp + 0xa0, sp + 0xb0), (sp + 0x108, sp + 0x110)]) : MemFrame M M' (FJ sp) :=
  h.mono fun a n hh => by simp only [FJ, outside_cons, outside_nil, and_true] at hh ⊢; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `JS` through `runJ`'s spills of `z` (`0x108/0xa0/0xa8`) and the `CALL`'s push -/
theorem jo_own (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {rk : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : JS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ)
    {S2 : State} {M2 : Memory} (hF : MemFrame S.mem M2 (FJ sp))
    (hrg : M2.regions = S.mem.regions) (fm : S2.mem = M2) (f4 : S2.regs 4 = S.regs 4) (f14 : S2.regs 14 = S.regs 14)
    (ffs : S2.fsBase = S.fsBase) (fx : S2.xmm 15 = S.xmm 15) (fdf : S2.df = S.df)
    (r108 : M2.readLE (sp + 0x108) 8 = pZ) (ra0 : M2.readLE (sp + 0xa0) 8 = lw) (ra8 : M2.readLE (sp + 0xa8) 8 = cZ) :
    JO R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S2 L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ := by
  have hk := hP.kf
  have hstw := hP.stkF.1
  unfold Apart at hstw
  obtain ⟨hw2, hown⟩ := WC.own hP h.jx.wc hF hrg (fun q hq => by
    simp only [FJ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a, (a + 8 ≤ sp - 8 ∨ sp ≤ a) → (a + 8 ≤ sp + 0xa0 ∨ sp + 0xb0 ≤ a) →
      (a + 8 ≤ sp + 0x108 ∨ sp + 0x110 ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a h0 h1 h2 =>
    hF.readLE a 8 (by simp only [FJ, outside_cons, outside_nil, and_true]; omega)
  have hhd : HdrEq st S.mem M2 := by
    refine ⟨?_, kF _ (by omega) (by omega) (by omega), kF _ (by omega) (by omega) (by omega)⟩
    have := kF (st + 0) (by omega) (by omega) (by omega); simpa using this
  subst fm
  exact ⟨⟨f4.trans h.jx.esp, f14.trans h.jx.e14, by rw [ffs]; exact h.jx.efs, fx.trans h.jx.ex15, fdf.trans h.jx.edf,
      hw2, h.jx.esl.keep (fun a k ha => hF.readLE a k (by
        simp only [SlotR] at ha; simp only [FJ, outside_cons, outside_nil, and_true]; omega)), h.jx.bud⟩,
    (kF _ (by omega) (by omega) (by omega)).trans h.s118, (kF _ (by omega) (by omega) (by omega)).trans h.sc8,
    (kF _ (by omega) (by omega) (by omega)).trans h.sd0, (kF _ (by omega) (by omega) (by omega)).trans h.s110,
    (kF _ (by omega) (by omega) (by omega)).trans h.sb8, (kF _ (by omega) (by omega) (by omega)).trans h.sc0,
    (kF _ (by omega) (by omega) (by omega)).trans h.s100, (kF _ (by omega) (by omega) (by omega)).trans h.s90,
    (kF _ (by omega) (by omega) (by omega)).trans h.s98, (kF _ (by omega) (by omega) (by omega)).trans h.sf8,
    (kF _ (by omega) (by omega) (by omega)).trans h.s80, (kF _ (by omega) (by omega) (by omega)).trans h.s88,
    r108, ra0, ra8,
    hown _ _ _ _ h.m1, h.c1p, hown _ _ _ _ h.m2, h.ap, hown _ _ _ _ h.z1, h.pz64, h.z1e, h.za1, h.za2,
    hown _ _ _ _ h.z2, h.pw64, h.z2e, h.wa1, h.wa2, h.wz, DZ.frm (LiveExt.refl R L1) hF.accessible hhd h.dz, h.pZ64, h.Ze,
    h.Za1, h.Za2, h.Zz1, h.Zz2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`setTl`: `JS` → `J9`** (see the module doc) -/
theorem setTl {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibNE.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {rk : Nat} {ret0 : W64}
    {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (K9 : ∀ S' : State,
      J9 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S' L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (h : JS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hml := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
  have hsp64 : sp < 2 ^ 64 := by omega
  have hsp2 : sp + 0x1b8 ≤ 2 ^ 48 := by omega
  have hw := h.jx.wc
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hcZ := h.dz.1
  have hlw := h.dz.2.2.2
  have hlm := h.lwm
  have hz2 := h.z2
  have hlc := hz2.2.1
  refine runJ ret0 Q sp pw lw cw pZ cZ S.mem hacc0 hsp8 hsp2 h.pw64 (by omega) h.pZ64 (by omega) S h.pc h.jx.esp rfl
    h.r0 h.r3 h.r2 h.r6 h.r7 h.r1 ?_ ?_
  · intro S2 M2 fpc f4 hEq f0 f1 f6 f5 f14 ffs fx fdf fm hF hrg r108 ra0 ra8
    have hO := jo_own hP h (fr_KE hsp8 hF) hrg fm (f4.trans h.jx.esp.symm) f14 ffs fx fdf r108 ra0 ra8
    subst hEq
    exact K9 S2 (hO.toJ9 fpc f0 f1 f6 hO.z2.2.2.1 hO.z2.2.2.2)
  · intro S2 M2 fpc f4 hne f0 f3 f1 f5 f14 ffs fx fdf fm hF hrg rra r108 ra0 ra8
    obtain ⟨a4, a14, am, afs, ax, adf⟩ := @atSp_eqs S2 sp
    have hO := jo_own hP h (S2 := atSp S2 sp) hF hrg (am.trans fm) (a4.trans h.jx.esp.symm) (a14.trans f14)
      (afs.trans ffs) (ax.trans fx) (adf.trans fdf) r108 ra0 ra8
    have hw2 := hO.jx.wc
    -- the copy's source / destination facts (only used when `lw > 0`)
    have hD : 8 * lw = 0 ∨ (pw + 8 * lw ≤ 2 ^ 48 ∧ M2.accessible pw (8 * lw) false = true ∧
        Apart pw (8 * lw) (sp - 8 - K) (K + 0x1c0) ∧ pZ + 8 * lw ≤ 2 ^ 48 ∧ M2.accessible pZ (8 * lw) true = true ∧
        Held R L1 pZ (8 * lw) ∧ Apart pZ (8 * lw) (sp - 8 - K) (K + 0x1c0)) := by
      rcases Nat.eq_zero_or_pos lw with e0 | lw0
      · left; omega
      · right
        have c0 : 0 < cZ := by omega
        have cw0 : 0 < cw := by omega
        obtain ⟨-, a2, a3, a4⟩ := hO.dz.2.1 c0
        obtain ⟨-, b2, b3, b4⟩ := hO.z2.1.2.1 cw0
        obtain ⟨-, w1, -, -⟩ := ZOK.ap hP hw2 c0 (hO.dz.2.2.1 c0)
        obtain ⟨v1, -⟩ := Loc.ap hP (hO.z2.1.2.2 cw0).1
        unfold Apart at w1 v1
        rw [← fm]
        exact ⟨by omega, Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ b3
          (Nat.le_refl _) (by omega)), by unfold Apart; omega, by omega,
          Janus.Arm64.Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega), a2.sub (Nat.le_refl _) (by omega),
          by unfold Apart; omega⟩
    refine mvCall hmv hmz hP hw2 (d := pZ) (src := pw) (n := 8 * lw) (by omega) h.pZ64 h.pw64 (by rw [am, fm]; exact hD)
      S2 fpc f4 (f14.trans h.jx.e14) (by rw [am]) (by rw [am, fm, rra]; decide) (fx.trans h.jx.ex15) (fdf.trans h.jx.edf) f0 f3 f1
      (fun junk fl x yh m zh kr dd hdd hF2 hLF2 hinv2 hcp hrg2 => ?_)
    obtain ⟨t4, t5, t14, tfs, tx, tdf, tpc, tm⟩ := @rs_regs S2 junk [] fl x yh m zh kr
    have hd : (dd = 0 ∧ 8 * lw = 0) ∨ (dd = pZ ∧ 8 * lw ≤ 8 * cZ ∧ 0 < cZ) := by
      rcases hdd with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e2, e1⟩
      · exact Or.inr ⟨e2, by omega, by omega⟩
    have e4 : (retState64 S2 junk [] fl x yh m zh kr).regs 4 = (atSp S2 sp).regs 4 := by
      rw [t4, f4, a4, bv_add8 hsp8 hsp64]
    have hF2' := hF2
    rw [← am] at hF2' hLF2
    have hO2 := hO.mv hP hd hF2' hLF2 (by rw [hrg2, am]) hinv2 _ e4 (t14.trans a14.symm) (tfs.trans afs.symm)
      (tx.trans ax.symm) (tdf.trans adf.symm) tm
    have hacc2 : m.accessible (sp - 8) 0x1c0 true = true := by
      rw [hF2.accessible, fm, hF.accessible]; exact hacc0
    refine runMv ret0 Q sp pw lw cw m hacc2 hsp8 hsp2 hO2.sf8 hO2.s80 hO2.s88 _
      (by rw [tpc, ra_eq (ra := mvR) f4 hsp64 (by rw [fm]; exact rra)]) (by rw [e4, a4]) tm
      (fun S3 g1 g4 g3 g0 g1' g6 g5 g14 gfs gx gdf => ?_)
    have hO3 := hO.mv hP hd hF2' hLF2 (by rw [hrg2, am]) hinv2 S3 (by rw [g4, a4])
      (g14.trans (t14.trans a14.symm)) (gfs.trans (tfs.trans afs.symm)) (gx.trans (tx.trans ax.symm))
      (gdf.trans (tdf.trans adf.symm)) g3
    have hv := hO.z2.2.2.1
    have hn := hO.z2.2.2.2
    rw [am] at hv hn
    refine K9 S3 (hO3.toJ9 g1 g0 g1' g6 ?_ ?_)
    · rw [← hv]; show S3.mem.readLE pZ (8 * lw) = S2.mem.readLE pw (8 * lw)
      rw [g3]; exact FvModexp.Asm.readLE_of_copied hcp
    · rcases hn with e | hne0
      · exact Or.inl e
      · rcases Nat.eq_zero_or_pos lw with e | lw0
        · exact Or.inl e
        right
        rw [g3, FvModexp.Asm.readLE_of_copied (cp_sub hcp (j := 8 * (lw - 1)) (k := 8) (by omega))]
        exact hne0

end

end FvModexp.Amd64.ExpEven
