import FvModexp.Proofs.Arm64.Exp.EvSetT

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `setT` — `JS` (`setJ`) → `J9` (`mvJ`) (agent infra)

`runJ` (spills, `jo_own`: `JS → JO`), then: same pointer → `JO.toJ9` (the value is `z2`'s); else
`memmove(pZ, pw, 8·lw)` (`lw = 0`: `mvCallZ`, else `mvCallW`), `JO.mv`, `runMv`, and the copied value.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem nv0 (m m' : Memory) (a a' : Nat) : natVal m a 0 = natVal m' a' 0 := rfl

theorem cp_sub {m0 m : Memory} {d s n j k : Nat} (h : Mem.Copied m0 m d s n) (hj : j + k ≤ n) :
    Mem.Copied m0 m (d + j) (s + j) k := fun i hi => by
  have := h (j + i) (by omega)
  rw [← Nat.add_assoc, ← Nat.add_assoc] at this
  exact this

theorem rs_regs {T : State} {junk : Nat → W64} {f : Flags} {v : Nat → BitVec 128} {m : Memory}
    {ex : Option (Nat × Nat)} {ep : Nat → Bool} :
    (retStateX T junk [] f v m ex ep).sp = T.sp ∧ (retStateX T junk [] f v m ex ep).regs 28 = T.regs 28 ∧
      (retStateX T junk [] f v m ex ep).regs 29 = T.regs 29 ∧
      (retStateX T junk [] f v m ex ep).regs 18 = T.regs 18 ∧
      (retStateX T junk [] f v m ex ep).pc = T.regs 30 ∧ (retStateX T junk [] f v m ex ep).mem = m := by
  simp [retStateX, callRegs_apply]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- `JS` through `runJ`'s spills of `z` (`272/168/176`) -/
theorem jo_own (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {rk : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : JS R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ)
    {S2 : State} {M2 : Memory} (hF : MemFrame S.mem M2 [(sp + 168, sp + 184), (sp + 272, sp + 280)])
    (hrg : M2.regions = S.mem.regions) (fm : S2.mem = M2) (fsp : S2.sp = S.sp) (f18 : S2.regs 18 = S.regs 18)
    (f28 : S2.regs 28 = S.regs 28) (f29 : S2.regs 29 = S.regs 29) (r272 : M2.readLE (sp + 272) 8 = pZ)
    (r168 : M2.readLE (sp + 168) 8 = lw) (r176 : M2.readLE (sp + 176) 8 = cZ) :
    JO R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S2 L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 448) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  obtain ⟨hw2, hown⟩ := WC.own hP h.jx.wc hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a, (a + 8 ≤ sp + 168 ∨ sp + 184 ≤ a) → (a + 8 ≤ sp + 272 ∨ sp + 280 ≤ a) →
      M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 =>
    hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hhd : HdrEq st S.mem M2 := by
    refine ⟨?_, kF _ (by omega) (by omega), kF _ (by omega) (by omega)⟩
    have := kF (st + 0) (by omega) (by omega); simpa using this
  subst fm
  exact ⟨⟨fsp.trans h.jx.esp, f28.trans h.jx.e28, f29.trans h.jx.e29, f18.trans h.jx.e18, hw2,
      h.jx.esl.keep (fun a k ha => hF.readLE a k (by
        simp only [SlotR] at ha; simp only [outside_cons, outside_nil, and_true]; omega)) (by omega), h.jx.bud⟩,
    (kF _ (by omega) (by omega)).trans h.s288, (kF _ (by omega) (by omega)).trans h.s208,
    (kF _ (by omega) (by omega)).trans h.s216, (kF _ (by omega) (by omega)).trans h.s280,
    (kF _ (by omega) (by omega)).trans h.s192, (kF _ (by omega) (by omega)).trans h.s200,
    (kF _ (by omega) (by omega)).trans h.s264, (kF _ (by omega) (by omega)).trans h.s152,
    (kF _ (by omega) (by omega)).trans h.s160, (kF _ (by omega) (by omega)).trans h.s256,
    (kF _ (by omega) (by omega)).trans h.s136, (kF _ (by omega) (by omega)).trans h.s144, r272, r168, r176,
    hown _ _ _ _ h.m1, h.c1p, hown _ _ _ _ h.m2, h.ap, hown _ _ _ _ h.z1, h.pz64, h.z1e, h.za1, h.za2,
    hown _ _ _ _ h.z2, h.pw64, h.z2e, h.wa1, h.wa2, h.wz, DZ.frm (LiveExt.refl R L1) hF.accessible hhd h.dz, h.pZ64, h.Ze,
    h.Za1, h.Za2, h.Zz1, h.Zz2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`setT`: `JS` → `J9`** (see the module doc) -/
theorem setT {impl : List Segment} (hmv : MemmoveLive (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive (LibNE.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {rk : Nat} {ret0 : BitVec 64}
    {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (K9 : ∀ S' : State,
      J9 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S' L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ →
      ReachesRet (LibNE.program.link impl) ret0 S' Q)
    (h : JS R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hw := h.jx.wc
  have hacc : S.mem.accessible (sp + 128) 320 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
  have hcZ := h.dz.1
  have hlw := h.dz.2.2.2
  have hlm := h.lwm
  refine runJ ret0 Q sp pw lw cw pZ cZ S.mem hal hsp2 hacc h.pw64 (by omega) h.pZ64 (by omega) S h.pc h.jx.esp rfl
    h.r0 h.r1 h.r3 h.r4 h.r5 h.r2 ?_ ?_
  · intro S2 M2 fpc fsp hEq f0 f2 f4 f18 f28 f29 fm hF hrg r272 r168 r176
    have hO := jo_own hP h hF hrg fm fsp f18 f28 f29 r272 r168 r176
    subst hEq
    exact K9 S2 (hO.toJ9 fpc f0 f2 f4 hO.z2.2.2.1 hO.z2.2.2.2)
  · intro S2 M2 fpc fsp hne f0 f1 f2 f30 f18 f28 f29 fm hF hrg r272 r168 r176
    have hO := jo_own hP h hF hrg fm fsp f18 f28 f29 r272 r168 r176
    have hw2 := hO.jx.wc
    have hacc2 : ∀ (m : Memory), (∀ a n w, m.accessible a n w = S2.mem.accessible a n w) →
        m.accessible (sp + 128) 320 true = true := fun m hm => by
      rw [hm, hw2.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
    rcases Nat.eq_zero_or_pos lw with e0 | lw0
    · subst e0
      refine mvCallZ hmz ret0 Q hP hw2 (ra := mvR) (by decide) (by decide) S2 fpc hO.jx.esp hO.jx.e28 rfl
        (by rw [f2]) f30 (fun junk f v m ex ep hF2 hLF2 hinv2 hrg2 => ?_)
      obtain ⟨t1, t28, t29, t18, tpc, tm⟩ := @rs_regs S2 junk f v m ex ep
      have hF2' : MemFrame S2.mem m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(0, 0 + 0)]) :=
        hF2.mono fun a n hh => by rw [outside_append] at hh; exact hh.1
      have hLF2' : LiveFrame S2.mem m L1 [(0, 0 + 0)] := ⟨fun a n hin _ => hLF2.readLE a n hin trivial⟩
      have hO2 := hO.mv hP (d := 0) (n := 0) (Or.inl ⟨rfl, rfl⟩) hF2' hLF2' hrg2 hinv2 _ t1 t28 t29 t18 tm
      refine runMv ret0 Q sp pw 0 cw m hal hsp2 (hacc2 m hF2.accessible) hO2.s256 hO2.s144 hO2.s136 _
        (by rw [tpc, f30]) hO2.jx.esp tm (fun S3 g1 g2 g3 g4 g5 g6 g18 g28 g29 => ?_)
      have hO3 := hO.mv hP (d := 0) (n := 0) (Or.inl ⟨rfl, rfl⟩) hF2' hLF2' hrg2 hinv2 S3 (g2.trans t1)
        (g28.trans t28) (g29.trans t29) (g18.trans t18) g3
      exact K9 S3 (hO3.toJ9 g1 g4 g5 g6 ((nv0 _ _ _ _).trans hO.z2.2.2.1) (Or.inl rfl))
    · have hz := h.dz
      have c0 : 0 < cZ := by omega
      have hz2 := hO.z2
      have cw0 : 0 < cw := by have := hz2.2.1; omega
      obtain ⟨-, a2, a3, a4⟩ := hO.dz.2.1 c0
      obtain ⟨-, b2, b3, b4⟩ := hz2.1.2.1 cw0
      obtain ⟨-, w1, -, -⟩ := ZOK.ap hP hw2 c0 (hO.dz.2.2.1 c0)
      obtain ⟨v1, -⟩ := Loc.ap hP (hz2.1.2.2 cw0).1
      have hlc := hz2.2.1
      unfold Apart at w1 v1
      refine mvCallW hmv ret0 Q hP hw2 (dst := pZ) (src := pw) (n := 8 * lw) (ra := mvR) (by decide) (by decide)
        (by omega) (by omega) (Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega)) (a2.sub (Nat.le_refl _)
          (by omega)) (by unfold Apart; omega) (by omega)
        (Memory.accessible_weaken _ (Memory.accessible_mono _ b3 (Nat.le_refl _) (by omega)))
        (by unfold Apart; omega) S2 fpc hO.jx.esp hO.jx.e28 rfl f0 f1 f2 f30
        (fun junk f v m ex ep hF2 hLF2 hinv2 hcp hrg2 => ?_)
      obtain ⟨t1, t28, t29, t18, tpc, tm⟩ := @rs_regs S2 junk f v m ex ep
      have hd : (pZ = 0 ∧ 8 * lw = 0) ∨ (pZ = pZ ∧ 8 * lw ≤ 8 * cZ ∧ 0 < cZ) := Or.inr ⟨rfl, by omega, c0⟩
      have hO2 := hO.mv hP hd hF2 hLF2 hrg2 hinv2 _ t1 t28 t29 t18 tm
      refine runMv ret0 Q sp pw lw cw m hal hsp2 (hacc2 m hF2.accessible) hO2.s256 hO2.s144 hO2.s136 _
        (by rw [tpc, f30]) hO2.jx.esp tm (fun S3 g1 g2 g3 g4 g5 g6 g18 g28 g29 => ?_)
      have hO3 := hO.mv hP hd hF2 hLF2 hrg2 hinv2 S3 (g2.trans t1) (g28.trans t28) (g29.trans t29)
        (g18.trans t18) g3
      refine K9 S3 (hO3.toJ9 g1 g4 g5 g6 ?_ ?_)
      · rw [← hz2.2.2.1]; show S3.mem.readLE pZ (8 * lw) = S2.mem.readLE pw (8 * lw)
        rw [g3]; exact FvModexp.Expmc.readLE_of_copied hcp
      · rcases hz2.2.2.2 with e | hne0
        · omega
        · right
          rw [g3, FvModexp.Expmc.readLE_of_copied (cp_sub hcp (j := 8 * (lw - 1)) (k := 8) (by omega))]
          exact hne0

end

end FvModexp.Arm64.ExpEven
