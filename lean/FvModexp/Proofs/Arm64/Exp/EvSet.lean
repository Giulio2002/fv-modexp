import FvModexp.Proofs.Arm64.Exp.EvSetP
import FvModexp.Proofs.Arm64.Exp.EvSetU

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): **`segSet`** — `J8` (`exp2R`) → `z = z.set(z2)` → `J9` (`mvJ`) (agent infra)

nat.go:58-69 (inlined `z.make(len z2)`), 93-94: `runS` → reuse (`JP.reuseJS`) / `makeslice(1, 1)` (`runM1`) /
`makeslice(l, l + 4)` (`runMN`) (`mkCall`, `JP.mkJS`) → `setT`. Budget: `∀ c ≤ ml + 4, allocCost (8c) + rk' ≤ rk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- `runtime.makeslice`'s contract address -/
abbrev mkE : Nat := 587344

theorem mkE_eq : Extracted.program.contractAddr "runtime.makeslice" = mkE := by decide

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`J8` → `J9`** (see the module doc) -/
theorem segSet {impl : List Segment} (hmv : MemmoveLive (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive (LibNE.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract (LibNE.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : ∀ c, c ≤ ml + 4 → allocCost (8 * c) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K9 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat),
      J9 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat}
    (h : J8 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := h.jx.wc
  have hacc : S.mem.accessible (sp + 128) 320 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
  have hcw := h.z2.1.1
  have hlw := h.z2.2.1
  have hrk0 : rk' ≤ rk := by have := hrk 0 (by omega); simp only [allocCost] at this; omega
  refine runS ret0 Q sp zp zc pw lw cw S.mem hal hsp2 hacc h.jx.esl.2.2.2.2.2.2.1 h.jx.esl.2.2.2.2.2.2.2.1 hzc
    h.pw64 (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r1 h.r2 ?_ ?_ ?_
  · intro S2 M2 fpc fsp hlz f0 f1 f3 f4 f5 f2 f18 f28 f29 fm hF hrg r256 r136 r144
    have hJ := j8_own hP hM hev h (hF.mono fun a n hh => by
      simp only [outside_cons, outside_nil, and_true] at hh ⊢; omega) hrg fm fsp f18 f28 f29
      r256 r136 r144
    exact setT hmv hmz hP (fun S' hj => K9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj) (hJ.reuseJS hP hrk0 fpc f0 f1 f2 f3 f4 f5 hlz)
  · intro S2 M2 fpc fsp hlz e1 f0 f1 f2 f30 f18 f28 f29 fm hF hrg r256 r136 r144
    subst e1
    have hJ := j8_own hP hM hev h (hF.mono fun a n hh => by
      simp only [outside_cons, outside_nil, and_true] at hh ⊢; omega) hrg fm fsp f18 f28 f29
      r256 r136 r144
    have hb := hJ.jx.bud
    have hr1 := hrk 1 (by omega)
    have hbs : blockSize (8 * 1) true ≤ b1 := by
      have := blockSize_le_allocCost (8 * 1) true; omega
    refine mkCall mkE_eq hmk ret0 Q hP hJ.jx.wc (n := 1) (c := 1) (ra := mk1R) (by decide) (by decide)
      (by decide) (by decide) (by decide) hbs S2 fpc hJ.jx.esp hJ.jx.e28 rfl f0 f1 f2 f30
      (fun ptr junk f v m ex ep hA => ?_)
    obtain ⟨t1, t28, t29, t18, tpc, tm, t0⟩ := @rs1_regs S2 junk ptr f v m ex ep
    have kA : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 448 → m.readLE a 8 = S2.mem.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    refine runM1 ret0 Q sp pw 1 cw m hal hsp2 (by rw [hA.macc, hJ.jx.wc.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega))
      ((kA _ (by omega) (by omega)).trans hJ.s256) ((kA _ (by omega) (by omega)).trans hJ.s136)
      ((kA _ (by omega) (by omega)).trans hJ.s144) _ (by rw [tpc, f30]) (by rw [t1, hJ.jx.esp]) tm
      (fun S3 g1 g2 g3 g4 g5 g6 g7 g8 g9 g18 g28 g29 => ?_)
    exact setT hmv hmz hP (fun S' hj => K9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj) (hJ.mkJS hP hA (c := 1) (by omega) (by decide) (by decide) ptr.isLt
      (bud_alloc hb hr1 hA.rc) S3 (g2.trans t1) (g28.trans t28) (g29.trans t29) (g18.trans t18) g3 g1 g4 g5 g9 g6 g7
      (g8.trans t0))
  · intro S2 M2 fpc fsp hlz e1 f0 f1 f2 f30 f18 f28 f29 fm hF hrg r256 r136 r144 r128
    have hJ := j8_own hP hM hev h hF hrg fm fsp f18 f28 f29 r256 r136 r144
    have hb := hJ.jx.bud
    have hlm := hJ.lwm
    have hr1 := hrk (lw + 4) (by omega)
    have hbs : blockSize (8 * (lw + 4)) true ≤ b1 := by
      have := blockSize_le_allocCost (8 * (lw + 4)) true; omega
    refine mkCall mkE_eq hmk ret0 Q hP hJ.jx.wc (n := lw) (c := lw + 4) (ra := mkNR) (by omega) (by omega)
      (by omega) (by decide) (by decide) hbs S2 fpc hJ.jx.esp hJ.jx.e28 rfl f0 f1 f2 f30
      (fun ptr junk f v m ex ep hA => ?_)
    obtain ⟨t1, t28, t29, t18, tpc, tm, t0⟩ := @rs1_regs S2 junk ptr f v m ex ep
    have kA : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 448 → m.readLE a 8 = S2.mem.readLE a 8 := fun a h1 h2 =>
      hA.keep a 8 (Or.inr ⟨h1, h2⟩)
    refine runMN ret0 Q sp pw lw cw m hal hsp2 (by rw [hA.macc, hJ.jx.wc.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega))
      ((kA _ (by omega) (by omega)).trans hJ.s256) ((kA _ (by omega) (by omega)).trans hJ.s136)
      ((kA _ (by omega) (by omega)).trans hJ.s144) ((kA _ (by omega) (by omega)).trans (by rw [fm]; exact r128)) _
      (by rw [tpc, f30]) (by rw [t1, hJ.jx.esp]) tm (fun S3 g1 g2 g3 g4 g5 g6 g7 g8 g9 g18 g28 g29 => ?_)
    exact setT hmv hmz hP (fun S' hj => K9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj) (hJ.mkJS hP hA (c := lw + 4) (by omega) (by omega) (by omega) ptr.isLt
      (bud_alloc hb hr1 hA.rc) S3 (g2.trans t1) (g28.trans t28) (g29.trans t29) (g18.trans t18) g3 g1 g4 g5 g9 g6 g7
      (g8.trans t0))

end

end FvModexp.Arm64.ExpEven
