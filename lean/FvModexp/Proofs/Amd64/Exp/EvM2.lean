import FvModexp.Proofs.Amd64.Exp.EvMulH
import FvModexp.Proofs.Amd64.Exp.EvM1R

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): **`segM2`** — `J13` (`trR`) → `u = z3.mul(stk, t mod 2^n, m2)` → `J14` (`mul2R`) (asm s63;
twin of infra's arm64 `EvM2`)

`runMul2` stores `m2` as the stack argument `y` and pushes `mul2R`; `mulPre` gives `Q.NatMul.MPre` (window
`[sp - 8 - W, sp + 80)`, reserve level `H = lvl4 + 8 ml + 64`); a stack callee with a possibly EMPTY destination `z3`
(`frmS_dst` + `stepC`); `z` survives; the product is located (`LN.of_sm`) with `EL` (`EL.of_res`).
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
/-- **`J13` → `J14`** (see the module doc) -/
theorem segM2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {W : Nat} (hmu : Q.DivRec.MulHypQE impl R ns W) (hWX : mulWX64 ≤ W) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hs16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → lvl4 s st mp ml l1 l2 + 8 * ml + 64 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : ∀ l1 l2 a c, l1 ≤ ml → l2 ≤ ml → a ≤ ml → c ≤ ml →
      mulCQ a c + stkRes (lvl4 s st mp ml l1 l2 + 8 * ml + 64) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K14 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 lw pZ cZ pu lu cu : Nat),
      J14 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 l1 l2 lw pZ cZ pu lu cu →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat}
    (h : J13 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct) :
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
  have hlt : lt ≤ ml := len_mlE h.t.2.2.2 h.t.2.2.1 (Nat.mod_lt _ (Nat.two_pow_pos _)) hnl
  have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
  have hl20 : 0 < l2 := by
    rcases Nat.eq_zero_or_pos l2 with e | e
    · have e0 := h.m2.2.2.1
      rw [e] at e0
      have : natVal s.mem mp ml / 2 ^ nE s mp ml = 0 := by rw [← e0]; rfl
      rw [this] at hodd; exact absurd hodd (by decide)
    · exact e
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have h198 : S.mem.readLE (sp + 0x198) 8 = st := h.jx.esl.2.2.2.2.2.2.2.2.1
  have hc3 : c3 < 2 ^ 40 := h.z3.1.1
  have hca : a2 ml (nE s mp ml) < 2 ^ 40 := h.m2.1.1
  have hq64 : q < 2 ^ 64 := by have := (h.m2.1.2.1 ha2).2.2.2; omega
  have hl3c := h.z3.2.1
  have hs16' := hs16 l1 l2 hl1 hl2
  have hltx : lt ≤ 2 ^ 12 := by omega
  have hl2x : l2 ≤ 2 ^ 12 := by omega
  have hrk' := hrk l1 l2 lt l2 hl1 hl2 hlt hl2
  refine runMul2 ret0 Q sp st q l2 (a2 ml (nE s mp ml)) p3 l3 c3 pt lt ct S.mem hacc0 hsp8 (by omega) h.s110
    h.sb8 h.sc0 h198 h.s100 h.s90 h.s98 hq64 (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r3 h.r1 ?_
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
  have hz3 := hown _ _ _ _ h.z3
  have ht0 := hown _ _ _ _ h.t
  have hzs := LZ.frm hP hw (LiveExt.refl R L1) hF.accessible hhd (d := 0) (n := 0)
    (fun a k _ hw0 _ => hF.readLE a k (by
      unfold Apart at hw0; simp only [outside_cons, outside_nil, and_true]; omega)) h.zs
    (fun _ => by unfold Apart; omega)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  have hsr := stkR_le (lvl4 s st mp ml l1 l2 + 8 * ml + 64) M2 st
  have hpre := mulPre hP hw2 hWK tsp tg tfs fm hz3 h.z3e ht0 hm2 (fun c0 c30 => h.t3 c0 c30)
    (fun c0 c30 => (h.ta2 c30).symm) hltx hl2x (Nat.le_trans (mulW64_le_X hltx hl2x) hWX) (m16 hlt hl2 hs16')
    (H := lvl4 s st mp ml l1 l2 + 8 * ml + 64) (m16H hlt hl2) (bud_q1 hb1 hrk' hsr)
  have hsp' : sp - 8 + 8 = sp := by omega
  refine mulCallE hap hns hmu _ (ra := mul2R) (ra_ev hap hnf 1306 (by decide)) f0 (by rw [tsp, fm, frd])
    r0 r3 r1 r7 r6 r8 r9 (by rw [rx15]; exact h.jx.ex15) (by rw [rdf]; exact h.jx.edf) h.p364 (by omega) hst64
    h.pt64 (by omega) (by omega) (by rw [tsp, hsp', fm]; exact ry0)
    (by rw [tsp, show sp - 8 + 16 = sp + 8 by omega, fm]; exact ry1)
    (by rw [tsp, show sp - 8 + 24 = sp + 0x10 by omega, fm]; exact ry2) hpre ?_
  intro s' hr e4 e5 e14 ex15 hrg' hq
  obtain ⟨efs, edf, pu, lu, cu, g0, g3, g1, hv, hN, hlc, -, hc40, L2, b2, hx, hb, hinv, hlv, hor, hfa, -, hsb, hF',
    hLF'⟩ := hq
  simp only [win, tsp] at hF'
  rw [fm] at hF' hLF' hrg' hv hsb hb
  rw [ht0.2.2.1, hm2.2.2.1] at hv
  rw [tg] at hinv
  have hor' : (pu = p3 ∧ cu = c3) ∨ (InRanges pu (8 * cu) R.rt ∧ ApartAll pu (8 * cu) L1) :=
    hor.imp id (fun h => h.2)
  have hrs := resSep_faE (fun c0 => (hz3.1.2.1 c0).2.1) hsb hfa
  obtain ⟨qd, kd, hds, hdl, hdw, hF'', hLF'', hapd⟩ := frmS_dst hP hz3 hF' hLF'
  obtain ⟨hw', hkc, -⟩ := stepC hP hw2 hds hdl hdw (stk := W) (above := 88) hWK (by decide) hF'' hLF'' hrg'
    hx hinv hsb
  have hk' := kk_push4 hsp8 hF hkc
  have hzs' := LZ.step hP hw2 (stk := W) (above := 88) hWK (by decide) hF'' hLF'' hx hsb hzs
    fun c0 => hapd _ _ c0 fun c30 => (h.tZ c30 c0).symm
  have hpu : pu < 2 ^ 64 := natOF_p64 hor hlv h.p364 (by omega)
  have hu := LN.of_sm hP hw2 hz3 hv hN hlc hc40 hlv hor' hx hsb hrs
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, f4]; exact bv_add8 hsp8 hspl
  have hjx := h.jx.call (hS4.trans h.jx.esp.symm) (e14.trans r14) (by rw [efs, rfs]) (ex15.trans rx15)
    (edf.trans rdf) hw' hk' (bud_qE hb1 hrk' hsr hb)
  exact K14 s' L2 b2 l1 l2 lw pZ cZ pu lu cu ⟨hjx, by rw [hr], hl1, g0, g3, g1,
    m_slot hk' 0x108 (by decide) (by decide) h.s108,
    m_slot hk' 0xa0 (by decide) (by decide) h.sa0, m_slot hk' 0xa8 (by decide) (by decide) h.sa8,
    hzs', h.pZ64, h.Ze, hu, hpu, EL.of_res h.z3e hw2.le hor',
    fun c0 cZ0 => apart_res hor' (h.zs.2.1 cZ0).2.1 (fun c30 => h.tZ c30 cZ0) c0⟩

end

end FvModexp.Amd64.ExpEven
