import FvModexp.Proofs.Amd64.Exp.EvSetP
import FvModexp.Proofs.Amd64.Exp.EvSetU

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `z = z.set(z2)` — `J8` → `J9` (asm s61; twin of infra's arm64 `EvSet`)

nat.go:58-69, 93-94: `runS` → reuse (`JP.reuseJS`) / `makeslice(Word, 1, 1)` (`mkCall`, `runM1`) /
`makeslice(Word, len, len + 4)` (`mkCall`, `runMN`) → `JS` (`JP.mkJS`) → `setTl` → `J9`. At each `CALL` the frame's
facts are kept at `atSp T sp` (the call state with `RSP` reset to `sp`). Budget: one allocation of at most
`ml + 4` words.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`J8` → `J9`** (see the module doc) -/
theorem segSet {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibNE.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : ∀ c, c ≤ ml + 4 → allocCost (8 * c) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K9 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat),
      J9 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : J8 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hml := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
  have hsp64 : sp < 2 ^ 64 := by omega
  have hsp2 : sp + 0x1b8 ≤ 2 ^ 48 := by omega
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := h.jx.wc
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hcw := h.z2.1.1
  have hlw := h.z2.2.1
  have hrk0 : rk' ≤ rk := by have := hrk 0 (by omega); simp only [allocCost] at this; omega
  refine runS ret0 Q sp zp zc pw lw cw S.mem hacc0 hsp8 hsp2 h.jx.esl.2.2.2.2.2.2.1 h.jx.esl.2.2.2.2.2.2.2.1 hzc
    h.pw64 (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r3 h.r1 ?_ ?_ ?_
  · intro S2 M2 fpc f4 hlz f0 f1 f3 f6 f7 f2 f5 f14 ffs fx fdf fm hF hrg rf8 r80 r88
    have hJ := j8_own hP hM hev h (fr_K0 hsp8 hF) hrg fm (f4.trans h.jx.esp.symm) f14 ffs fx fdf rf8 r80 r88
    exact setTl hmv hmz hP (fun S' hj => K9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      (hJ.reuseJS hP hrk0 fpc f0 f1 f3 f6 f7 f2 hlz)
  · intro S2 M2 fpc f4 hlz e1 f0 f3 f1 f5 f14 ffs fx fdf fm hF hrg rra rf8 r80 r88
    subst e1
    obtain ⟨a4, a14, am, afs, ax, adf⟩ := @atSp_eqs S2 sp
    have hJ := j8_own hP hM hev h (S2 := atSp S2 sp) (fr_K1 hsp8 hF) hrg (am.trans fm) (a4.trans h.jx.esp.symm)
      (a14.trans f14) (afs.trans ffs) (ax.trans fx) (adf.trans fdf) rf8 r80 r88
    have hb := hJ.jx.bud
    have hr1 := hrk 1 (by omega)
    have hbs : blockSize (8 * 1) true ≤ b1 := by
      have := blockSize_le_allocCost (8 * 1) true; omega
    refine mkCall hmk hP hJ.jx.wc (n := 1) (c := 1) (by decide) (by decide) (by decide) hbs S2 fpc f4
      (f14.trans h.jx.e14) (by rw [am]) (by rw [am, fm, rra]; decide) f0 f3 f1
      (fun ptr junk fl x yh m zh kr hA => ?_)
    obtain ⟨t4, t5, t14, tfs, tx, tdf, tpc, tm⟩ := @rs_regs S2 junk [ptr] fl x yh m zh kr
    have kA : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 0x1b8 → m.readLE a 8 = (atSp S2 sp).mem.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    refine runM1 ret0 Q sp pw 1 cw m (by rw [hA.macc, am, fm, hF.accessible]; exact hacc0) hsp8 hsp2
      ((kA _ (by omega) (by omega)).trans hJ.sf8) ((kA _ (by omega) (by omega)).trans hJ.s80)
      ((kA _ (by omega) (by omega)).trans hJ.s88) _
      (by rw [tpc, ra_eq (ra := mk1R) f4 hsp64 (by rw [fm]; exact rra)]) (by rw [t4, f4, bv_add8 hsp8 hsp64]) tm
      (fun S3 g1 g4 gm g0 g1' g3 g6 g7 g2 g5 g14 gfs gx gdf => ?_)
    exact setTl hmv hmz hP (fun S' hj => K9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      (hJ.mkJS hP hA (c := 1) (by omega) (by decide) (by decide) ptr.isLt (bud_alloc hb hr1 hA.rc) S3
        (g4.trans a4.symm) (g14.trans (t14.trans a14.symm)) (gfs.trans (tfs.trans afs.symm))
        (gx.trans (tx.trans ax.symm)) (gdf.trans (tdf.trans adf.symm)) gm g1 g0 g1' g3 g6
        (g7.trans (rs_r0.trans (bv_of_toNat rfl))) g2)
  · intro S2 M2 fpc f4 hlz e1 f0 f3 f1 f5 f14 ffs fx fdf fm hF hrg rra rf8 r80 r88 r78
    obtain ⟨a4, a14, am, afs, ax, adf⟩ := @atSp_eqs S2 sp
    have hJ := j8_own hP hM hev h (S2 := atSp S2 sp) hF hrg (am.trans fm) (a4.trans h.jx.esp.symm)
      (a14.trans f14) (afs.trans ffs) (ax.trans fx) (adf.trans fdf) rf8 r80 r88
    have hb := hJ.jx.bud
    have hlm := hJ.lwm
    have hr1 := hrk (lw + 4) (by omega)
    have hbs : blockSize (8 * (lw + 4)) true ≤ b1 := by
      have := blockSize_le_allocCost (8 * (lw + 4)) true; omega
    refine mkCall hmk hP hJ.jx.wc (n := lw) (c := lw + 4) (by omega) (by omega) (by omega) hbs S2 fpc f4
      (f14.trans h.jx.e14) (by rw [am]) (by rw [am, fm, rra]; decide) f0 f3 f1
      (fun ptr junk fl x yh m zh kr hA => ?_)
    obtain ⟨t4, t5, t14, tfs, tx, tdf, tpc, tm⟩ := @rs_regs S2 junk [ptr] fl x yh m zh kr
    have kA : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 0x1b8 → m.readLE a 8 = (atSp S2 sp).mem.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    refine runMN ret0 Q sp pw lw cw m (by rw [hA.macc, am, fm, hF.accessible]; exact hacc0) hsp8 hsp2
      ((kA _ (by omega) (by omega)).trans hJ.sf8) ((kA _ (by omega) (by omega)).trans hJ.s80)
      ((kA _ (by omega) (by omega)).trans hJ.s88) ((kA _ (by omega) (by omega)).trans (by rw [am, fm]; exact r78)) _
      (by rw [tpc, ra_eq (ra := mkNR) f4 hsp64 (by rw [fm]; exact rra)]) (by rw [t4, f4, bv_add8 hsp8 hsp64]) tm
      (fun S3 g1 g4 gm g0 g1' g3 g6 g7 g2 g5 g14 gfs gx gdf => ?_)
    exact setTl hmv hmz hP (fun S' hj => K9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      (hJ.mkJS hP hA (c := lw + 4) (by omega) (by omega) (by omega) ptr.isLt (bud_alloc hb hr1 hA.rc) S3
        (g4.trans a4.symm) (g14.trans (t14.trans a14.symm)) (gfs.trans (tfs.trans afs.symm))
        (gx.trans (tx.trans ax.symm)) (gdf.trans (tdf.trans adf.symm)) gm g1 g0 g1' g3 g6
        (g7.trans (rs_r0.trans (bv_of_toNat rfl))) g2)

end

end FvModexp.Amd64.ExpEven
