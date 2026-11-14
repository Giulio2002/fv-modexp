import FvModexp.Proofs.Amd64.Exp.EvMulH
import FvModexp.Proofs.Amd64.Exp.EvM1R

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): **`segM1`** — `J11` (`miR`) → `z2 = z2.mul(stk, z3, m2inv)` → `J12` (`mul1R`) (asm s63;
twin of infra's arm64 `EvM1`)

`runMul1` stores `m2inv` as the stack argument `y` and pushes `mul1R`; `mulPre` gives `Q.NatMul.MPre` (window
`[sp - 8 - W, sp + 80)`, reserve level `H = lvl4 + 8 ml + 64`); a stack callee with a possibly EMPTY destination `z2`
(`frmS_dst` + `stepC`); `m2`, `z`, `z3` survive; the product is located (`LN.of_sm`) with `EL` (`EL.of_res`).
Budget: `MPost`'s `b1 − (mulCQ + stkR H M) + stkR H M' ≤ b'` (`bud_q`). Slot reads through small lemmas (`m_own`,
`m_kc`; PERF LESSON s62).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J11` → `J12`** (see the module doc) -/
theorem segM1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {W : Nat} (hmu : Q.DivRec.MulHypQE impl R ns W) (hWX : mulWX64 ≤ W) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hs16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → lvl4 s st mp ml l1 l2 + 8 * ml + 64 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : ∀ l1 l2 a c, l1 ≤ ml → l2 ≤ ml → a ≤ ml → c ≤ ml →
      mulCQ a c + stkRes (lvl4 s st mp ml l1 l2 + 8 * ml + 64) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K12 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat),
      J12 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 : Nat}
    (h : J11 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hl1 := h.l1m
  have hl2 : l2 ≤ ml := by have := h.m2.2.1; simp only [a2] at this; omega
  have hl3 : l3 ≤ ml := len_mlE h.z3.2.2.2 h.z3.2.2.1 (Exp.subMod2N_spec _ _ _).1 hnl
  have hl4 : l4 ≤ ml := len_mlE h.mi.2.2.2 h.mi.2.2.1 (mi_lt _ _) hnl
  have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
  have hl40 : 0 < l4 := by
    rcases Nat.eq_zero_or_pos l4 with e | e
    · have e0 := h.mi.2.2.1
      rw [e] at e0
      have := mi_pos hodd hn0 (X := natVal s.mem mp ml / 2 ^ nE s mp ml)
      have e1 : vMi s mp ml = 0 := by rw [← e0]; rfl
      exact absurd e1 (Nat.pos_iff_ne_zero.mp this)
    · exact e
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have h198 : S.mem.readLE (sp + 0x198) 8 = st := h.jx.esl.2.2.2.2.2.2.2.2.1
  have hc3 : c3 < 2 ^ 40 := h.z3.1.1
  have hc4 : c4 < 2 ^ 40 := h.mi.1.1
  have hcw : cw < 2 ^ 40 := h.z2.1.1
  have hl3c := h.z3.2.1
  have hl4c := h.mi.2.1
  have hlwc := h.z2.2.1
  have hs16' := hs16 l1 l2 hl1 hl2
  have hl3x : l3 ≤ 2 ^ 12 := by omega
  have hl4x : l4 ≤ 2 ^ 12 := by omega
  have hrk' := hrk l1 l2 l3 l4 hl1 hl2 hl3 hl4
  refine runMul1 ret0 Q sp st pw lw cw p3 l3 c3 p4 l4 c4 S.mem hacc0 hsp8 (by omega) h.sf8 h.s80 h.s88 h198
    h.s100 h.s90 h.s98 h.p464 (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r3 h.r1 ?_
  have hspl : sp < 2 ^ 64 := by omega
  have hst64 : st < 2 ^ 64 := by have := hP.stk0.2.2.2.1; omega
  intro S2 M2 f0 f4 fm hF hrg frd ry0 ry1 ry2 r0 r3 r1 r7 r6 r8 r9 r5 r14 rfs rx15 rdf
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (own4 sp K hsp8)
  have hhd : HdrEq st S.mem M2 := by
    have kF : ∀ a, (a + 8 ≤ sp - 8 ∨ sp + 0x18 ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 =>
      hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hstw := hP.stkF.1
    unfold Apart at hstw
    refine ⟨?_, kF _ (by omega), kF _ (by omega)⟩
    have := kF (st + 0) (by omega); simpa using this
  have hm2 := hown _ _ _ _ h.m2
  have hz2 := hown _ _ _ _ h.z2
  have hz3 := hown _ _ _ _ h.z3
  have hmi := hown _ _ _ _ h.mi
  have hzs := LZ.frm hP hw (LiveExt.refl R L1) hF.accessible hhd (d := 0) (n := 0)
    (fun a k _ hw0 _ => hF.readLE a k (by
      unfold Apart at hw0; simp only [outside_cons, outside_nil, and_true]; omega)) h.zs
    (fun _ => by unfold Apart; omega)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  have hsr := stkR_le (lvl4 s st mp ml l1 l2 + 8 * ml + 64) M2 st
  have hpre := mulPre hP hw2 hWK tsp tg tfs fm hz2 h.z2e hz3 hmi (fun c0 cw0 => h.tw c0 cw0)
    (fun c0 cw0 => h.iw c0 cw0) hl3x hl4x (Nat.le_trans (mulW64_le_X hl3x hl4x) hWX) (m16 hl3 hl4 hs16')
    (H := lvl4 s st mp ml l1 l2 + 8 * ml + 64) (m16H hl3 hl4) (bud_q1 hb1 hrk' hsr)
  have hsp' : sp - 8 + 8 = sp := by omega
  refine mulCallE hap hns hmu _ (ra := mul1R) (ra_ev hap hnf 1200 (by decide)) f0 (by rw [tsp, fm, frd])
    r0 r3 r1 r7 r6 r8 r9 (by rw [rx15]; exact h.jx.ex15) (by rw [rdf]; exact h.jx.edf) h.pw64 (by omega) hst64
    h.p364 (by omega) (by omega) (by rw [tsp, hsp', fm]; exact ry0)
    (by rw [tsp, show sp - 8 + 16 = sp + 8 by omega, fm]; exact ry1)
    (by rw [tsp, show sp - 8 + 24 = sp + 0x10 by omega, fm]; exact ry2) hpre ?_
  intro s' hr e4 e5 e14 ex15 hrg' hq
  obtain ⟨efs, edf, pt, lt, ct, g0, g3, g1, hv, hN, hlc, -, hc40, L2, b2, hx, hb, hinv, hlv, hor, hfa, -, hsb, hF',
    hLF'⟩ := hq
  simp only [win, tsp] at hF'
  rw [fm] at hF' hLF' hrg' hv hsb hb
  rw [hz3.2.2.1, hmi.2.2.1] at hv
  rw [tg] at hinv
  have hor' : (pt = pw ∧ ct = cw) ∨ (InRanges pt (8 * ct) R.rt ∧ ApartAll pt (8 * ct) L1) :=
    hor.imp id (fun h => h.2)
  have hrs := resSep_faE (fun c0 => (hz2.1.2.1 c0).2.1) hsb hfa
  obtain ⟨qd, kd, hds, hdl, hdw, hF'', hLF'', hapd⟩ := frmS_dst hP hz2 hF' hLF'
  obtain ⟨hw', hkc, hkeep⟩ := stepC hP hw2 hds hdl hdw (stk := W) (above := 88) hWK (by decide) hF'' hLF'' hrg'
    hx hinv hsb
  have hk' := kk_push4 hsp8 hF hkc
  have hm2' := hkeep _ _ _ _ hm2 fun c0 => hapd _ _ c0 fun cw0 => (h.wa2 cw0).symm
  have hz3' := hkeep _ _ _ _ hz3 fun c0 => hapd _ _ c0 fun cw0 => h.tw c0 cw0
  have hzs' := LZ.step hP hw2 (stk := W) (above := 88) hWK (by decide) hF'' hLF'' hx hsb hzs
    fun c0 => hapd _ _ c0 fun cw0 => h.Zz2 c0 cw0
  have hpt : pt < 2 ^ 64 := natOF_p64 hor hlv h.pw64 (by omega)
  have ht := LN.of_sm hP hw2 hz2 hv hN hlc hc40 hlv hor' hx hsb hrs
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, f4]; exact bv_add8 hsp8 hspl
  have hjx := h.jx.call (hS4.trans h.jx.esp.symm) (e14.trans r14) (by rw [efs, rfs]) (ex15.trans rx15)
    (edf.trans rdf) hw' hk' (bud_qE hb1 hrk' hsr hb)
  exact K12 s' L2 b2 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct ⟨hjx, by rw [hr], hl1,
    g0, g3, g1,
    m_slot hk' 0x110 (by decide) (by decide) h.s110, m_slot hk' 0xb8 (by decide) (by decide) h.sb8,
    m_slot hk' 0xc0 (by decide) (by decide) h.sc0, m_slot hk' 0x108 (by decide) (by decide) h.s108,
    m_slot hk' 0xa0 (by decide) (by decide) h.sa0, m_slot hk' 0xa8 (by decide) (by decide) h.sa8,
    m_slot hk' 0x100 (by decide) (by decide) h.s100, m_slot hk' 0x90 (by decide) (by decide) h.s90,
    m_slot hk' 0x98 (by decide) (by decide) h.s98,
    hm2', hzs', h.pZ64, h.Ze, h.Za2, hz3', h.p364, h.z3e, h.ta2, h.tZ, ht, hpt, EL.of_res h.z2e hw2.le hor',
    apart_res hor' (h.m2.1.2.1 ha2).2.1 (fun cw0 => h.wa2 cw0),
    fun c0 cZ0 => apart_res hor' (h.zs.2.1 cZ0).2.1 (fun cw0 => (h.Zz2 cZ0 cw0).symm) c0,
    fun c0 c30 => apart_res hor' (h.z3.1.2.1 c30).2.1 (fun cw0 => (h.tw c30 cw0).symm) c0⟩

end

end FvModexp.Amd64.ExpEven
