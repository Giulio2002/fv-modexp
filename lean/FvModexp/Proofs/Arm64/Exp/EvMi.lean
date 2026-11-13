import FvModexp.Proofs.Arm64.Exp.EvMiP
import FvModexp.Proofs.Arm64.Exp.EvMiR
import FvModexp.Proofs.Arm64.Exp.EvSm

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): **`segMi`** — `J10` (`smR`) → `m2inv := m1.modularInverseModPowerOfTwo(stk, m2, n)` →
`J11` (`miR`) (agent infra)

`runMi` spills `z3`; `miPre` gives `ModInv.PreL` (window `[sp - (240 + kc), sp + 72)`, level `lvl4`); the callee is a
stack user (`stepC` with destination `m1`'s array, `StackBackL` from `ModInv.Post`). `m2`, `z2`, `z`, `z3` are apart
from `m1` and survive; `m2inv` is located (`LN.of_sm`: `m1`'s array or fresh) and apart from them (`apart_res`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J10` → `J11`** (see the module doc) -/
theorem segMi {impl : List Segment} (hap : ImplApart Extracted.program impl) {kc : Nat}
    {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} (hE : MiEns impl R kc sqC mlC)
    (hK : 240 + kc ≤ K) (hkc : 4608 ≤ kc)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hs16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → lvl4 s st mp ml l1 l2 + 8 * ModInv.NW (nE s mp ml) + 72 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml →
      ModInv.cost (sqC (lvl4 s st mp ml l1 l2)) (mlC (lvl4 s st mp ml l1 l2)) (nE s mp ml) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K11 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 : Nat),
      J11 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 : Nat}
    (h : J10 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hKs := hP.1.2.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 448) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hl1 : l1 ≤ ml := nlen_bd' h.m1.2.2.2 (by rw [h.m1.2.2.1]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hl2 : l2 ≤ ml := by have := h.m2.2.1; simp only [a2] at this; omega
  have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
  have hl20 : 0 < l2 := by
    rcases Nat.eq_zero_or_pos l2 with e | e
    · have e0 := h.m2.2.2.1
      rw [e] at e0
      have : natVal s.mem mp ml / 2 ^ nE s mp ml = 0 := by rw [← e0]; rfl
      rw [this] at hodd; exact absurd hodd (by decide)
    · exact e
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  have hp1 : p1 < 2 ^ 64 := by have := (h.m1.1.2.1 h.c1p).2.2.2; omega
  have hacc : S.mem.accessible (sp + 136) 312 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega)
  have h184 : S.mem.readLE (sp + 184) 8 = nE s mp ml := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine runMi ret0 Q sp st p1 l1 c1 q l2 (a2 ml (nE s mp ml)) (nE s mp ml) p3 l3 c3 S.mem hal hsp2 hacc
    h.s288 h.s208 h.s216 h.jx.esl.2.2.2.2.2.2.2.2.1 h.s280 h.s192 h.s200 h184 h.p364
    (by have := h.z3.2.1; have := h.z3.1.1; omega) (by have := h.z3.1.1; omega) S h.pc h.jx.esp rfl h.r0 h.r1 h.r2 ?_
  intro S2 M2 f0 fsp r0 r1 r2 r3 r4 r5 r6 r7 f30 f18 f28 f29 fm hF hrg r264 r152 r160
  -- the spills: `WC` and the locals at `M2`
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a, (a + 8 ≤ sp + 152 ∨ sp + 168 ≤ a) → (a + 8 ≤ sp + 264 ∨ sp + 272 ≤ a) →
      M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 =>
    hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hhd : HdrEq st S.mem M2 := by
    refine ⟨?_, kF _ (by omega) (by omega), kF _ (by omega) (by omega)⟩
    have := kF (st + 0) (by omega) (by omega); simpa using this
  have hesl := h.jx.esl.keep (fun a k ha => hF.readLE a k (by
    simp only [SlotR] at ha; simp only [outside_cons, outside_nil, and_true]; omega)) (by omega)
  have hm1 := hown _ _ _ _ h.m1
  have hm2 := hown _ _ _ _ h.m2
  have hz2 := hown _ _ _ _ h.z2
  have hz3 := hown _ _ _ _ h.z3
  have hzs := LZ.frm hP hw (LiveExt.refl R L1) hF.accessible hhd (d := 0) (n := 0)
    (fun a k _ hw0 _ => hF.readLE a k (by
      unfold Apart at hw0; simp only [outside_cons, outside_nil, and_true]; omega)) h.zs
    (fun _ => by unfold Apart; omega)
  have hS2 : S2.sp = BitVec.ofNat 64 sp := fsp.trans h.jx.esp
  have h28 : S2.regs 28 = BitVec.ofNat 64 g := f28.trans h.jx.e28
  have hsN : S2.sp.toNat = sp := by rw [hS2, BitVec.toNat_ofNat]; omega
  have hgN : (S2.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  -- the call
  have hpre := miPre hP hw2 hK hkc hS2 h28 fm (sqC := sqC) (mlC := mlC) f30 ⟨by decide, by decide⟩
    hm1 h.c1p hp1 hm2 hl20 (by omega) hodd h.ap (by omega) (by omega) (hs16 l1 l2 hl1 hl2)
    (bud_pre hb1 (hrk l1 l2 hl1 hl2))
  have hS := CallNE.hypSum hap libW_sub (hE (lvl4 s st mp ml l1 l2) b1 L1 p1 l1 c1 st q l2 (a2 ml (nE s mp ml))
    (nE s mp ml))
  refine ReachesRet.call_regions hS (by rw [f0, modInv_a]) ⟨?_, ?_, hpre⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg' => ?_
  · rw [f30, LibCalls.tN (by simp only [miR]; omega)]; exact ra_ev hap libW_nf 177 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7, trivial⟩
  · obtain ⟨p4, l4, c4, g0, g1, g2, hv, hN, hlc, hc40, L2, b2, hx, hb, hinv, hlv, hor, hsb, hF', hLF, hrs⟩ := hq
    simp only [winA, hsN, ModInv.K, ModInv.A] at hF'
    rw [fm] at hF' hLF hrg' hv hsb hrs
    rw [hm2.2.2.1] at hv
    rw [hgN] at hinv
    have hloc1 := (hm1.1.2.2 h.c1p).1
    obtain ⟨dw, -, -, -⟩ := Loc.ap hP hloc1
    obtain ⟨hw', hk, hkeep⟩ := stepC hP hw2 (Loc.sub hloc1) (Loc.subL hloc1) h.c1p dw (stk := 240 + kc)
      (above := 72) hK (by omega) hF' hLF hrg' hx hinv hsb
    have hm2' := hkeep _ _ _ _ hm2 fun _ => h.ap
    have hz2' := hkeep _ _ _ _ hz2 h.wa1
    have hz3' := hkeep _ _ _ _ hz3 h.ta1
    have hzs' := LZ.step hP hw2 (stk := 240 + kc) (above := 72) hK (by omega) hF' hLF hx hsb hzs h.Za1
    have hp4 : p4 < 2 ^ 64 := by rw [← g0]; exact BitVec.isLt _
    have hmi := LN.of_sm hP hw2 hm1 hv hN hlc hc40 hlv hor hx hsb hrs
    have k : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 448 → s'.mem.readLE a 8 = M2.readLE a 8 := fun a h1 h2 =>
      hk a 8 (Or.inr ⟨h1, h2⟩)
    have hjx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s s' L2 b2 (lvl4 s st mp ml l1 l2) rk' :=
      ⟨e1.trans hS2, e2.trans h28, e3.trans (f29.trans h.jx.e29), e4.trans (f18.trans h.jx.e18), hw',
        hesl.keep (fun a k' ha => hk a k' (by simp only [SlotR] at ha; omega)) (by omega),
        bud_step hb1 (hrk l1 l2 hl1 hl2) hb⟩
    exact K11 s' L2 b2 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 ⟨hjx, hr.trans f30, hl1,
      BitVec.eq_of_toNat_eq (by rw [g0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp4]),
      BitVec.eq_of_toNat_eq (by rw [g1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
      BitVec.eq_of_toNat_eq (by rw [g2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s280,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s192,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s200,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s256,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s136,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s144,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s272,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s168,
      by rw [k _ (by omega) (by omega), kF _ (by omega) (by omega)]; exact h.s176,
      by rw [k _ (by omega) (by omega)]; exact r264,
      by rw [k _ (by omega) (by omega)]; exact r152,
      by rw [k _ (by omega) (by omega)]; exact r160,
      hm2', hz2', h.pw64, h.z2e, h.wa2, hzs', h.pZ64, h.Ze, h.Za2, h.Zz2, hz3', h.p364, h.z3e, h.ta2, h.tw, h.tZ, hmi, hp4,
      EL.of_res (fun e => absurd e (by have := h.c1p; omega)) hw2.le hor,
      apart_res hor (h.m2.1.2.1 ha2).2.1 (fun _ => h.ap.symm),
      fun c0 cw0 => apart_res hor (h.z2.1.2.1 cw0).2.1 (fun _ => (h.wa1 cw0).symm) c0,
      fun c0 cZ0 => apart_res hor (h.zs.2.1 cZ0).2.1 (fun _ => (h.Za1 cZ0).symm) c0,
      fun c0 c30 => apart_res hor (h.z3.1.2.1 c30).2.1 (fun _ => (h.ta1 c30).symm) c0⟩

end

end FvModexp.Arm64.ExpEven
