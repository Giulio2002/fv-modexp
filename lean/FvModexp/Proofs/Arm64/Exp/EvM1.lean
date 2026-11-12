import FvModexp.Proofs.Arm64.Exp.EvMulP
import FvModexp.Proofs.Arm64.Exp.EvJ12
import FvModexp.Proofs.Arm64.Exp.EvSm

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): **`segM1`** — `J11` (`miR`) → `z2 = z2.mul(stk, z1, m2inv)` → `J12` (`mul1R`) (agent infra)

`runM1`: `R3 = stk`, `R4..R6 = z3` (`264/152/160`), `R7..R9 = m2inv` (`X0..X2`), `R0..R2 = z2` (`256/136/144`),
`CALL nat.mul`. Premise `MulHypG` (empty `z3` tolerated); `mulPreG`; stack callee with a possibly EMPTY destination
(`frmS_dst` + `stepC0`); `m2`, `z`, `z3` survive; the product is located (`LN.of_sm`) with `EL` (`EL.of_res`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `miR` → `nat.mul`'s entry -/
theorem runM1 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st pw lw cw p3 l3 c3 : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 false = true)
    (h368 : M.readLE (sp + 368) 8 = st) (h264 : M.readLE (sp + 264) 8 = p3) (h152 : M.readLE (sp + 152) 8 = l3)
    (h160 : M.readLE (sp + 160) 8 = c3) (h256 : M.readLE (sp + 256) 8 = pw) (h136 : M.readLE (sp + 136) 8 = lw)
    (h144 : M.readLE (sp + 144) 8 = cw)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 miR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1814128 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pw → S'.regs 1 = BitVec.ofNat 64 lw → S'.regs 2 = BitVec.ofNat 64 cw →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 p3 → S'.regs 5 = BitVec.ofNat 64 l3 →
      S'.regs 6 = BitVec.ofNat 64 c3 → S'.regs 7 = S.regs 0 → S'.regs 8 = S.regs 1 → S'.regs 9 = S.regs 2 →
      S'.regs 30 = BitVec.ofNat 64 mul1R → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
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
  janus_run [h368, h264, h152, h160, h256, h136, h144, hacc, hal] until [1814128]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J11` → `J12`** (see the module doc) -/
theorem segM1 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypG impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ K) (haM : aboveM ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hs16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → ℓ4 s st mp ml l1 l2 + 8 * ml + 64 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : ∀ l1 l2 a c, l1 ≤ ml → l2 ≤ ml → a ≤ ml → c ≤ ml → mlC (ℓ4 s st mp ml l1 l2) a c + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K12 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat),
      J12 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 : Nat}
    (h : J11 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hKs := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hl1 := h.l1m
  have hl2 : l2 ≤ ml := by have := h.m2.2.1; simp only [a2] at this; omega
  have hml := hP.2.2.2.2.2.2.1
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hgN : (S.regs 28).toNat = g := by rw [h.jx.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hacc : S.mem.accessible (sp + 128) 320 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  have hl3 : l3 ≤ ml := len_ml h.z3.2.2.2 h.z3.2.2.1 (Exp.subMod2N_spec _ _ _).1 hnl
  have hl4 : l4 ≤ ml := len_ml h.mi.2.2.2 h.mi.2.2.1 (mi_lt _ _) hnl
  have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
  have hl40 : 0 < l4 := by
    rcases Nat.eq_zero_or_pos l4 with e | e
    · have e0 := h.mi.2.2.1
      rw [e] at e0
      have := mi_pos hodd hn0 (X := natVal s.mem mp ml / 2 ^ nE s mp ml)
      have e1 : vMi s mp ml = 0 := by rw [← e0]; rfl
      simp only [vMi] at e1; omega
    · exact e
  have hst48 := hP.stk0.2.2.2.1
  have hc3 : c3 < 2 ^ 40 := h.z3.1.1
  have hc4 : c4 < 2 ^ 40 := h.mi.1.1
  have hcw : cw < 2 ^ 40 := h.z2.1.1
  have hl3c := h.z3.2.1
  have hl4c := h.mi.2.1
  have hlwc := h.z2.2.1
  refine runM1 ret0 Q sp st pw lw cw p3 l3 c3 S.mem hal hsp2 hacc h.jx.esl.2.2.2.2.2.2.2.2.1 h.s264 h.s152 h.s160
    h.s256 h.s136 h.s144 S h.pc h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r30 r18 r28 r29
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  have hgN' : (S'.regs 28).toNat = g := by rw [r28]; exact hgN
  have hlen : stLen S'.mem st = ℓ4 s st mp ml l1 l2 := by rw [fm]; exact hw.len
  have hpre := mulPreG hP hw hkM haM (fsp.trans h.jx.esp) (r28.trans h.jx.e28) fm h.z2 h.z2e h.z3 h.mi
    (fun c0 cw0 => h.tw c0 cw0) (fun c0 cw0 => h.iw c0 cw0) (by omega) (by omega)
    (by have := hs16 l1 l2 hl1 hl2; omega) (c := mlC (stLen S'.mem st) l3 l4)
    (by rw [hlen]; exact bud_pre hb1 (hrk l1 l2 l3 l4 hl1 hl2 hl3 hl4))
  have hS := CallNE.hypSum hap hns (hmu b1 L1 (BitVec.ofNat 64 pw) (BitVec.ofNat 64 lw) (BitVec.ofNat 64 cw)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 p3) (BitVec.ofNat 64 l3) (BitVec.ofNat 64 c3) (BitVec.ofNat 64 p4)
    (BitVec.ofNat 64 l4) (BitVec.ofNat 64 c4))
  have t1 := LibCalls.tN h.pw64
  have t2 := LibCalls.tN (show lw < 2 ^ 64 by omega)
  have t3 := LibCalls.tN (show cw < 2 ^ 64 by omega)
  have t4 := LibCalls.tN (show st < 2 ^ 64 by omega)
  have t5 := LibCalls.tN h.p364
  have t6 := LibCalls.tN (show l3 < 2 ^ 64 by omega)
  have t7 := LibCalls.tN (show c3 < 2 ^ 64 by omega)
  have t8 := LibCalls.tN h.p464
  have t9 := LibCalls.tN (show l4 < 2 ^ 64 by omega)
  have t10 := LibCalls.tN (show c4 < 2 ^ 64 by omega)
  refine ReachesRet.call_regions hS (by rw [f0, mul_a]) ⟨?_, ?_, ?_⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [mul1R]; omega)]
    exact ra_ev hap hnf 188 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7.trans h.r0, r8.trans h.r1, r9.trans h.r2, trivial⟩
  · rw [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]; exact hpre
  · simp only [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] at hq
    obtain ⟨⟨pt, lt, ct, g0, g1, g2, L2, b2, ⟨hv, hN, hlc, hc40, hlv, hor⟩, ⟨hx, hb, hinv⟩, hsb, hfa, hF, hLF⟩, -⟩ := hq
    simp only [winA, hsN'] at hF
    rw [fm] at hF hLF hrg hsb hv
    rw [fm, hw.len] at hb
    rw [h.z3.2.2.1, h.mi.2.2.1] at hv
    rw [hgN'] at hinv
    have hor' : (pt = pw ∧ ct = cw) ∨ (InRanges pt (8 * ct) R.rt ∧ ApartAll pt (8 * ct) L1) :=
      hor.imp id (fun h => h.2)
    have hrs := resSep_of_fa (fun c0 => (h.z2.1.2.1 c0).2.1) hsb hfa
    obtain ⟨qd, kd, hds, hdl, hdw, hF', hLF', hapd⟩ :=
      frmS_dst hP h.z2 (stk := stkM) (above := aboveM) hkM (by omega) hF hLF
    obtain ⟨hw', hk, hkeep⟩ := stepC0 hP hw hds hdl hdw hkM (by omega) hF' hLF' hrg hx hinv hsb
    have hjx := h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw' hk (by omega)
      (bud_step hb1 (hrk l1 l2 l3 l4 hl1 hl2 hl3 hl4) hb)
    have hm2' := hkeep _ _ _ _ h.m2 fun c0 => hapd _ _ c0 fun cw0 => (h.wa2 cw0).symm
    have hz3' := hkeep _ _ _ _ h.z3 fun c0 => hapd _ _ c0 fun cw0 => h.tw c0 cw0
    have hzs' := LZ.step hP hw (stk := stkM) (above := aboveM) hkM (by omega) hF' hLF' hx hsb h.zs
      fun c0 => hapd _ _ c0 fun cw0 => h.Zz2 c0 cw0
    have hpt : pt < 2 ^ 64 := natOF_p64 hor hlv h.pw64 (by omega)
    have ht := LN.of_sm hP hw h.z2 hv hN hlc hc40 hlv hor' hx hsb hrs
    have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
    have k : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 448 → s'.mem.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 => by
      rw [hk a 8 (Or.inr ⟨h1, h2⟩)]
    exact K12 s' L2 b2 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct ⟨hjx, hr.trans r30, hl1, g0, g1, g2,
      by rw [k _ (by omega) (by omega)]; exact h.s280, by rw [k _ (by omega) (by omega)]; exact h.s192,
      by rw [k _ (by omega) (by omega)]; exact h.s200, by rw [k _ (by omega) (by omega)]; exact h.s272,
      by rw [k _ (by omega) (by omega)]; exact h.s168, by rw [k _ (by omega) (by omega)]; exact h.s176,
      by rw [k _ (by omega) (by omega)]; exact h.s264, by rw [k _ (by omega) (by omega)]; exact h.s152,
      by rw [k _ (by omega) (by omega)]; exact h.s160,
      hm2', hzs', h.pZ64, h.Ze, h.Za2, hz3', h.p364, h.z3e, h.ta2, h.tZ, ht, hpt, EL.of_res h.z2e hw.le hor',
      apart_res hor' (h.m2.1.2.1 ha2).2.1 (fun cw0 => h.wa2 cw0),
      fun c0 cZ0 => apart_res hor' (h.zs.2.1 cZ0).2.1 (fun cw0 => (h.Zz2 cZ0 cw0).symm) c0,
      fun c0 c30 => apart_res hor' (h.z3.1.2.1 c30).2.1 (fun cw0 => (h.tw c30 cw0).symm) c0⟩

end

end FvModexp.Arm64.ExpEven
