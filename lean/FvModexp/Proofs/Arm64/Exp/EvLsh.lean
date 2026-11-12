import FvModexp.Proofs.Arm64.Exp.EvJ
import FvModexp.Proofs.Arm64.Exp.EvCalls
import FvModexp.Proofs.Arm64.Nat.LshDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `nat1R` → `m1 = m1.lsh(natOne, n)` → `lshR` (agent infra)

`runL`: `R3, R4` = `natOne`'s pointer / length (`LDP` at `natOneA`), `R5` = its capacity, `R6 = n` (slot 184), `CALL
nat.lsh` (entry `0x1b3af0`, return `lshR`). `segL` (`J1 → J2`): the call with asm's `Lsh.Hyp2`; `lsh` needs
`len natOne + n/64 + 1 = a1 + 1` words but the scratch has `a1`, so the result is FRESH (`c1 ≥ a1 + 1`), of value
`1 · 2^n`; the stack is untouched (`nonStk`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

theorem lsh_a : segAddr Extracted.program ExpHyp.fnLsh = 1784560 := by decide
theorem natOneA_v : natOneA = 7356432 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `nat1R` → `nat.lsh`'s entry -/
theorem runL {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp n op : Nat) (M : Memory)
    (h0 : M.readLE 7356432 8 = op) (h8 : M.readLE (7356432 + 8) 8 = 1) (h16 : M.readLE (7356432 + 16) 8 = 1)
    (hacc : M.accessible 7356432 24 false = true) (h184 : M.readLE (sp + 184) 8 = n)
    (hacc2 : M.accessible (sp + 184) 8 false = true) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 nat1R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1784560 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = BitVec.ofNat 64 op →
      S'.regs 4 = BitVec.ofNat 64 1 → S'.regs 5 = BitVec.ofNat 64 1 → S'.regs 6 = BitVec.ofNat 64 n →
      S'.regs 30 = BitVec.ofNat 64 lshR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
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
  janus_run [h0, h8, h16, h184, hacc, hacc2, hal] until [1784560]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | rfl | omega | skip)
  rw [← eS, hsp]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J1` → `J2`** (see the module doc) -/
theorem segL {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ K) (haL : aboveL ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : makeCost (a1 (nE s mp ml) + 1) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K2 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 : Nat),
      J2 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p : Nat}
    (h : J1 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hgN : (S.regs 28).toNat = g := by rw [h.jx.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  obtain ⟨op, ⟨o0, o8, o16, o1, oA, -, -, oa, o48, oh, ow⟩, -, ⟨-, -, -, -, -, -, -, -, -, ohE, -⟩, hsaE⟩ :=
    natOne_at hP hw hsN hkL haL (lo := sp - 8) (hi := sp + 8) (by omega) (by omega)
  have hd := h.d1
  obtain ⟨dw, dh, dg, -⟩ := Loc.ap hP (hd.2.2 (by simp only [a1]; omega)).1
  have hdo : Apart p (8 * a1 (nE s mp ml)) op 8 :=
    Loc.apart (hd.2.2 (by simp only [a1]; omega)).1 (by simp only [a1]; omega) ohE (hsaE (by omega)).2
  rw [natOneA_v] at o0 o8 o16 oA
  have h184 : S.mem.readLE (sp + 184) 8 = (nE s mp ml) := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hacc : S.mem.accessible (sp + 184) 8 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  refine runL ret0 Q sp (nE s mp ml) op S.mem o0 o8 o16 oA h184 hacc hal hsp2 S h.pc h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r30 r18 r28 r29
  have hS := CallNE.hypSum hap hns (hlh b1 L1 (BitVec.ofNat 64 p) (BitVec.ofNat 64 (a1 (nE s mp ml)))
    (BitVec.ofNat 64 (a1 (nE s mp ml))) (BitVec.ofNat 64 op) (BitVec.ofNat 64 1) (BitVec.ofNat 64 1) (BitVec.ofNat 64 (nE s mp ml)))
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  have hgN' : (S'.regs 28).toNat = g := by rw [r28]; exact hgN
  have hp48 : p < 2 ^ 64 := by have := (hd.2.1 (by simp only [a1]; omega)).2.2.2; omega
  refine ReachesRet.call_regions hS (by rw [f0, ← lsh_a]; rfl) ⟨?_, ?_, ?_⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [lshR]; omega)]; exact ra_ev hap hnf 54 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0.trans h.r0, r1.trans h.r1, r2.trans h.r2, r3, r4, r5, r6, trivial⟩
  · rw [LibCalls.tN hp48, LibCalls.tN (by simp only [a1]; omega), LibCalls.tN (by omega),
      LibCalls.tN (by decide), LibCalls.tN (by omega)]
    refine ⟨⟨CallW.callEnv_of (hw.cenv hP) (fsp.trans h.jx.esp) (r28.trans h.jx.e28) fm hkL haL, hsv,
      Nat.le_refl _, hd.wr hP hsN' hgN' fm hkL haL, ⟨by omega, by rw [fm]; exact oa, o48, oh, ?_⟩, by omega,
      Or.inr fun _ _ => hdo, ?_, by rw [hgN', fm]; exact hw.inv⟩, hn0, by omega⟩
    · simp only [winA, win, hsN', List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
        and_true] at ow ⊢
      omega
    · have := h.jx.bud
      rw [show 1 + nE s mp ml / 64 + 1 = a1 (nE s mp ml) + 1 by simp only [a1]; omega]; omega
  · rw [LibCalls.tN hp48, LibCalls.tN (by simp only [a1]; omega), LibCalls.tN (by omega),
      LibCalls.tN (by decide), LibCalls.tN (by omega)] at hq
    obtain ⟨p', l', c', g0, g1, g2, L2, b2, hres, hcap, ⟨hx, hb, hinv⟩, hF, hLF⟩ := hq
    rw [show 1 + nE s mp ml / 64 + 1 = a1 (nE s mp ml) + 1 by simp only [a1]; omega] at hb
    simp only [winA, hsN'] at hF
    rw [fm] at hF hLF hres hrg
    rw [hgN'] at hinv
    obtain ⟨hF', hLF', hsb, ehd⟩ := nonStk hw.sok hx hF hLF (hP.st_cw hkL haL) (out1_of_apart dh)
    obtain ⟨hw', hk, -⟩ := stepC hP hw (Loc.sub (hd.2.2 (by simp only [a1]; omega)).1)
      (Loc.subL (hd.2.2 (by simp only [a1]; omega)).1) (by simp only [a1]; omega) dw hkL haL hF' hLF' hrg hx hinv hsb
    have hm1 := LN.of_res hP hw hd hres hx hsb (fun _ hne => absurd ehd hne)
    have hv1 : natVal S.mem op 1 = 1 := by simpa only [natVal, Nat.mul_one] using o1
    rw [hv1, Nat.one_mul] at hm1
    have hc1 : 0 < c' := by have := hcap (by simp only [a1]; omega); omega
    refine K2 s' L2 b2 p' l' c' ⟨?_, hr.trans r30, g0, g1, g2, ?_, hm1, hc1⟩
    · exact h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw' hk
        (by omega) (by have := h.jx.bud; omega)
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact h.s224

end

end FvModexp.Arm64.ExpEven
