import FvModexp.Proofs.Arm64.Exp.EvJ3
import FvModexp.Proofs.Arm64.Exp.EvE1
import FvModexp.Proofs.Common.ExpPow2

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `nat4R` → `z2 = z2.expNN(stk, x, y, m2, false)` → `exp2R` (agent infra)

`runE2`: as `runE1` with `R10..R12 = m2` (slots `280/192/200`). `segE2` (`J7 → J8`): the premise
`EvenHyp.ExpNNHypNE1` (`m2 = M / 2^n` is odd: the odd disjunct, `Exp.tz_spec`), `ExpN.NPre` from `npre_of`; `m1`,
`m2`, `z1` survive (`stepC`, apart from the scratch `t`); the result is located (`LN.of_expN`); an empty result
(possibly `nil`) is kept as `(X0, 0, 0)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `nat4R` → `nat.expNN`'s entry (`m2` from the slots `280/192/200`) -/
theorem runE2 {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp st xp xl xc yp yl yc p1 l1 c1 : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 184) 264 false = true)
    (h368 : M.readLE (sp + 368) 8 = st) (h376 : M.readLE (sp + 376) 8 = xp) (h384 : M.readLE (sp + 384) 8 = xl)
    (h392 : M.readLE (sp + 392) 8 = xc) (h400 : M.readLE (sp + 400) 8 = yp) (h408 : M.readLE (sp + 408) 8 = yl)
    (h416 : M.readLE (sp + 416) 8 = yc) (h280 : M.readLE (sp + 280) 8 = p1) (h192 : M.readLE (sp + 192) 8 = l1)
    (h200 : M.readLE (sp + 200) 8 = c1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 nat4R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1786544 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = BitVec.ofNat 64 st →
      S'.regs 4 = BitVec.ofNat 64 xp → S'.regs 5 = BitVec.ofNat 64 xl → S'.regs 6 = BitVec.ofNat 64 xc →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl → S'.regs 9 = BitVec.ofNat 64 yc →
      S'.regs 10 = BitVec.ofNat 64 p1 → S'.regs 11 = BitVec.ofNat 64 l1 → S'.regs 12 = BitVec.ofNat 64 c1 →
      S'.regs 13 = BitVec.ofNat 64 0 →
      S'.regs 30 = BitVec.ofNat 64 exp2R → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
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
  janus_run [h368, h376, h384, h392, h400, h408, h416, h280, h192, h200, hacc, hal] until [1786544]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

/-- `log2` of the odd part `M / 2^n` of the modulus -/
@[reducible] def lg2 (s : State) (mp ml : Nat) : Nat := Nat.log2 (natVal s.mem mp ml / 2 ^ nE s mp ml)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J7` → `J8`** (see the module doc) -/
theorem segE2 {impl : List Segment} (hap : ImplApart Extracted.program impl)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : EvenHyp.ExpNNHypNE1 impl R KN costF needR costR needS needP costS costP)
    (hKN : 4304 ≤ KN) (hKN1 : KN + 1312 ≤ K) (hKN2 : KN + 288 ≤ 2 ^ 20)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hst : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → NStkE needR needS needP xl yl l2 (ℓ4 s st mp ml l1 l2) (lg2 s mp ml))
    {rk rk' : Nat}
    (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml →
      NBudE costF costR costS costP xl yl l2 (ℓ4 s st mp ml l1 l2) (lg2 s mp ml) ≤ rk ∧
      ExpN.NCost costF costR costS costP xl yl l2 (ℓ4 s st mp ml l1 l2) (lg2 s mp ml) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K8 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw : Nat),
      J8 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz t : Nat}
    (h : J7 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz t) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxc := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyl := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hyp, hyc, -, -, -⟩ :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hm1 := h.m1
  have hm2 := h.m2
  have hz1 := h.z1
  have hd4 := h.d4
  have hb1 := h.jx.bud
  have hl1 : l1 ≤ ml := nlen_bd' hm1.2.2.2 (by rw [hm1.2.2.1]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hl2 : l2 ≤ ml := by have := hm2.2.1; simp only [a2] at this; omega
  have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
  have hv2 : natVal S.mem q l2 = natVal s.mem mp ml / 2 ^ nE s mp ml := hm2.2.2.1
  have hl20 : 0 < l2 := by
    rcases Nat.eq_zero_or_pos l2 with e | e
    · have e0 : natVal S.mem q l2 = 0 := by rw [e]; rfl
      rw [hv2] at e0; rw [e0] at hodd; exact absurd hodd (by decide)
    · exact e
  have hk0 : 0 < 2 * max l1 l2 := by omega
  have hrl := (hd4.2.2 hk0).1
  obtain ⟨dw, -, -, -⟩ := Loc.ap hP hrl
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hgN : (S.regs 28).toNat = g := by rw [h.jx.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hacc : S.mem.accessible (sp + 184) 264 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  have hesl := h.jx.esl
  have hlg : Nat.log2 (natVal S.mem q l2) = lg2 s mp ml := by rw [hv2]
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hst l1 l2 hl1 hl2
  obtain ⟨hrk1, hrk2⟩ := hrk l1 l2 hl1 hl2
  refine runE2 ret0 Q sp st xp xl xc yp yl yc q l2 (a2 ml (nE s mp ml)) S.mem hal hsp2 hacc hesl.2.2.2.2.2.2.2.2.1
    hesl.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.2.1
    hesl.2.2.2.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hesl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.s280 h.s192 h.s200 S h.pc h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r30 r18 r28 r29
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  have hgN' : (S'.regs 28).toNat = g := by rw [r28]; exact hgN
  obtain ⟨-, -, -, xv⟩ := obj_at hP hw hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
    (fun h0 => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).2.2.2.2.2.1) hsN' fm (stk := 0) (above := 0)
    (by omega) (by omega)
  obtain ⟨-, -, -, yv⟩ := obj_at hP hw hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.1
    hP.2.2.2.2.2.2.2.2.2.2.1 (by omega)
    (fun h0 => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).2.2.2.2.2.2.1) hsN' fm (stk := 0) (above := 0)
    (by omega) (by omega)
  have hS := CallNE.hypSum hap libN_sub
    (hE b1 L1 t (2 * max l1 l2) (2 * max l1 l2) st xp xl xc yp yl yc q l2 (a2 ml (nE s mp ml)) 0)
  have hnp := npre_of hP hw (fsp.trans h.jx.esp) (r28.trans h.jx.e28) fm hKN hKN1 hKN2 hm2 hl20 (by omega)
    hd4 hk0 h.tm2 (costF := costF) (needR := needR) (costR := costR) (needS := needS) (needP := needP)
    (costS := costS) (costP := costP)
    (by rw [hw.len]; exact hs1) (by rw [hw.len]; exact hs2) (by rw [hw.len]; exact hs3)
    (by rw [hw.len, hlg]; exact hs4) (by rw [hw.len, hlg]; exact Nat.le_trans hrk1 hb1)
  refine ReachesRet.call_regions hS (by rw [f0, expN_a]) ⟨?_, ?_, ?_⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [exp2R]; omega)]; exact ra_ev hap libN_nf 105 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0.trans h.r0, r1.trans h.r1, r2.trans h.r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, trivial⟩
  · refine ⟨by rw [hgN', hsN']; exact hnp, Or.inl (by rw [fm, hv2]; exact hodd)⟩
  · obtain ⟨⟨p, l, c, g0, g1, g2, hv, hN, hlc, hc64, L2, b2, hx, hb, hinv, hlv, hres, hsb, hF, hLF, hrs⟩, hc40, hel⟩ := hq
    have tc : (s'.regs 2).toNat = c := by rw [g2, BitVec.toNat_ofNat]; omega
    rw [tc] at hc40
    simp only [winA, hsN'] at hF
    rw [fm] at hF hLF hrg hsb hrs hv hb
    rw [hgN'] at hinv
    rw [hw.len, hlg] at hb
    rw [xv, yv, hv2] at hv
    obtain ⟨hw', hk, hkeep⟩ := stepC hP hw (Loc.sub hrl) (Loc.subL hrl) hk0 dw (stk := KN + 1312) (above := 120)
      (by omega) (by omega) hF hLF hrg hx hinv hsb
    have hz := LN.of_expN hP hw hd4 hv hN hlc hc40 hlv hres hx hsb hrs
    have hjx := h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw' hk (by omega)
      (bud_step hb1 hrk2 hb)
    have hm1' := hkeep _ _ _ _ hm1 fun _ => h.tm1.symm
    have hm2' := hkeep _ _ _ _ hm2 fun _ => h.tm2.symm
    have hz1' := hkeep _ _ _ _ hz1 fun c0 => (h.tz1 c0).symm
    have k288 := hk (sp + 288) 8 (Or.inr ⟨by omega, by omega⟩)
    have k208 := hk (sp + 208) 8 (Or.inr ⟨by omega, by omega⟩)
    have k216 := hk (sp + 216) 8 (Or.inr ⟨by omega, by omega⟩)
    have k280 := hk (sp + 280) 8 (Or.inr ⟨by omega, by omega⟩)
    have k192 := hk (sp + 192) 8 (Or.inr ⟨by omega, by omega⟩)
    have k200 := hk (sp + 200) 8 (Or.inr ⟨by omega, by omega⟩)
    have k224 := hk (sp + 224) 8 (Or.inr ⟨by omega, by omega⟩)
    have k264 := hk (sp + 264) 8 (Or.inr ⟨by omega, by omega⟩)
    have k152 := hk (sp + 152) 8 (Or.inr ⟨by omega, by omega⟩)
    have k160 := hk (sp + 160) 8 (Or.inr ⟨by omega, by omega⟩)
    rcases Nat.eq_zero_or_pos c with c0 | c0
    · -- empty result (possibly `nil`): only its register value is kept
      subst c0
      have hl0 : l = 0 := by omega
      subst hl0
      have hz0 : LN R L s.mem st s'.mem L2 (s'.regs 0).toNat 0 0
          (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml)) :=
        ⟨⟨by decide, fun h0 => absurd h0 (Nat.lt_irrefl 0), fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩, Nat.le_refl _,
          by rw [← hz.2.2.1]; rfl, Or.inl rfl⟩
      exact K8 s' L2 b2 p1 l1 c1 q l2 pz lz cz (s'.regs 0).toNat 0 0 ⟨hjx, hr.trans r30,
        (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)])), g1, g2,
        by rw [k288]; exact h.s288, by rw [k208]; exact h.s208, by rw [k216]; exact h.s216,
        by rw [k280]; exact h.s280, by rw [k192]; exact h.s192, by rw [k200]; exact h.s200,
        by rw [k224]; exact h.s224, by rw [k264]; exact h.s264, by rw [k152]; exact h.s152,
        by rw [k160]; exact h.s160, hm1', h.c1p, hm2', h.ap, hz1', h.pz64, h.z1e, h.za1, h.za2, hz0, BitVec.isLt _,
        fun h0 => absurd h0 (Nat.lt_irrefl 0), fun h0 => absurd h0 (Nat.lt_irrefl 0),
        fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
    · have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
      have hza : ∀ (u n : Nat), Held R L1 u n → Apart t (8 * (2 * max l1 l2)) u n → Apart p (8 * c) u n := by
        intro u n hh ht
        rcases hres with ⟨e, -⟩ | ⟨rfl, rfl⟩ | ⟨hin, hap'⟩
        · omega
        · exact ht
        · exact hfresh hh hap' hin
      exact K8 s' L2 b2 p1 l1 c1 q l2 pz lz cz p l c ⟨hjx, hr.trans r30, g0, g1, g2,
        by rw [k288]; exact h.s288, by rw [k208]; exact h.s208, by rw [k216]; exact h.s216,
        by rw [k280]; exact h.s280, by rw [k192]; exact h.s192, by rw [k200]; exact h.s200,
        by rw [k224]; exact h.s224, by rw [k264]; exact h.s264, by rw [k152]; exact h.s152,
        by rw [k160]; exact h.s160, hm1', h.c1p, hm2', h.ap, hz1', h.pz64, h.z1e, h.za1, h.za2, hz,
        by have := (hlv c0).2.2.2; omega,
        fun _ => hza _ _ (hm1.1.2.1 h.c1p).2.1 h.tm1, fun _ => hza _ _ (hm2.1.2.1 ha2).2.1 h.tm2,
        fun _ c1 => hza _ _ (hz1.1.2.1 c1).2.1 (h.tz1 c1)⟩

end

end FvModexp.Arm64.ExpEven
