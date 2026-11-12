import FvModexp.Proofs.Arm64.Exp.EvJ
import FvModexp.Proofs.Arm64.Exp.EvCalls
import FvModexp.Proofs.Arm64.Nat.RshDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `nat2R` → `m2 = m2.rsh(m, n)` → `rshR` (agent infra)

`runR`: `R3..R5 = m` (slots 424/432/440), `R6 = n` (slot 184), `CALL nat.rsh` (entry `0x1b3dd0`, return `rshR`).
`segR` (`J3 → J4`): asm's `Rsh.Hyp`; `rsh` needs `ml - n/64` words = the scratch's capacity, so the result is the
scratch array itself (`NatRes` reuse), of value `M / 2^n`; `m1` survives (`stepC`, apart from the scratch).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem rsh_a : segAddr Extracted.program Rsh.fn = 1785296 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `nat2R` → `nat.rsh`'s entry -/
theorem runR {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp mp ml mc n : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 184) 264 false = true)
    (h424 : M.readLE (sp + 424) 8 = mp) (h432 : M.readLE (sp + 432) 8 = ml) (h440 : M.readLE (sp + 440) 8 = mc)
    (h184 : M.readLE (sp + 184) 8 = n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 nat2R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1785296 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = BitVec.ofNat 64 mp →
      S'.regs 4 = BitVec.ofNat 64 ml → S'.regs 5 = BitVec.ofNat 64 mc → S'.regs 6 = BitVec.ofNat 64 n →
      S'.regs 30 = BitVec.ofNat 64 rshR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at KN
  generalize e1 : S.regs 1 = x1 at KN
  generalize e2 : S.regs 2 = x2 at KN
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  janus_run [h424, h432, h440, h184, hacc, hal] until [1785296]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J3` → `J4`** (see the module doc) -/
theorem segR {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (hkR : stkR ≤ K) (haR : aboveR ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : makeCost (a2 ml (nE s mp ml)) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K4 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 : Nat),
      J4 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q : Nat}
    (h : J3 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml0 := hP.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hmO, hmacc, hm48, hmN, hmz, -, -, hmp, ⟨hmc40, hmlc⟩, -⟩ :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have ha2 : 0 < a2 ml (nE s mp ml) ∧ a2 ml (nE s mp ml) ≤ 128 := by simp only [a2]; omega
  have hw := h.jx.wc
  have hd := h.d2
  have hb1 := h.jx.bud
  have hdl := (hd.2.2 ha2.1).1
  obtain ⟨dw, dh, -, -⟩ := Loc.ap hP hdl
  have hq48 : q + 8 * a2 ml (nE s mp ml) ≤ 2 ^ 48 := (hd.2.1 ha2.1).2.2.2
  have hdm : Apart q (8 * a2 ml (nE s mp ml)) mp (8 * ml) := Loc.apart hdl ha2.1 hmO.1 fun _ => hmO.2.2.2
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hgN : (S.regs 28).toNat = g := by rw [h.jx.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hacc : S.mem.accessible (sp + 184) 264 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  have hesl := h.jx.esl
  refine runR ret0 Q sp mp ml mc (nE s mp ml) S.mem hal hsp2 hacc hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 S h.pc h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r30 r18 r28 r29
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  have hgN' : (S'.regs 28).toNat = g := by rw [r28]; exact hgN
  obtain ⟨xR, xN, -, xv⟩ := obj_at hP hw hmO hmacc hm48 hmN (by omega) hmz hsN' fm hkR haR
  have hS := CallNE.hypSum hap hns (hrh b1 L1 (BitVec.ofNat 64 q) (BitVec.ofNat 64 (a2 ml (nE s mp ml)))
    (BitVec.ofNat 64 (a2 ml (nE s mp ml))) (BitVec.ofNat 64 mp) (BitVec.ofNat 64 ml) (BitVec.ofNat 64 mc)
    (BitVec.ofNat 64 (nE s mp ml)))
  have tq := LibCalls.tN (show q < 2 ^ 64 by omega)
  have ta := LibCalls.tN (show a2 ml (nE s mp ml) < 2 ^ 64 by omega)
  have tm := LibCalls.tN (show mp < 2 ^ 64 by omega)
  have tl := LibCalls.tN (show ml < 2 ^ 64 by omega)
  have tc := LibCalls.tN (show mc < 2 ^ 64 by omega)
  have tn := LibCalls.tN (show nE s mp ml < 2 ^ 64 by omega)
  refine ReachesRet.call_regions hS (by rw [f0, rsh_a]) ⟨?_, ?_, ?_⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [rshR]; omega)]; exact ra_ev hap hnf 65 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0.trans h.r0, r1.trans h.r1, r2.trans h.r2, r3, r4, r5, r6, trivial⟩
  · rw [tq, ta, tm, tl, tc, tn]
    refine ⟨⟨CallW.callEnv_of (hw.cenv hP) (fsp.trans h.jx.esp) (r28.trans h.jx.e28) fm hkR haR, hsv,
      Nat.le_refl _, hd.wr hP hsN' hgN' fm hkR haR, xR, by omega, fun _ => hdm, by rw [fm]; exact xN, hml0,
      Or.inl hn0, bud_pre hb1 hrk, by rw [hgN', fm]; exact hw.inv⟩, hmlc, hmc40⟩
  · rw [tq, ta, tm, tl, tn] at hq
    obtain ⟨p', l', c', g0, g1, g2, L2, b2, hres, -, ⟨hx, hb, hinv⟩, hF, hLF⟩ := hq
    simp only [winA, hsN'] at hF
    rw [fm] at hF hLF hres hrg
    rw [hgN'] at hinv
    obtain ⟨hF', hLF', hsb, ehd⟩ := nonStk hw.sok hx hF hLF (hP.st_cw hkR haR) (out1_of_apart dh)
    obtain ⟨hw', hk, hkeep⟩ := stepC hP hw (Loc.sub hdl) (Loc.subL hdl) ha2.1 dw hkR haR hF' hLF' hrg hx hinv hsb
    obtain ⟨rfl, rfl⟩ := hres.2.2.2.2.2.1 (Nat.le_refl _)
    have hm2 := LN.of_res hP hw hd hres hx hsb (fun _ hne => absurd ehd hne)
    rw [xv] at hm2
    refine K4 s' L2 b2 p1 l1 c1 p' l' ⟨h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw'
      hk (by omega) (bud_step hb1 hrk hb), hr.trans r30, g0, g1, g2, ?_, ?_, ?_,
      hkeep _ _ _ _ h.m1 fun _ => h.ap.symm, h.c1p, hm2, h.ap⟩
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact h.s288
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact h.s208
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact h.s216

end

end FvModexp.Arm64.ExpEven
