import FvModexp.Proofs.Amd64.Exp.EvMiP
import FvModexp.Proofs.Amd64.Exp.EvMiR
import FvModexp.Proofs.Amd64.Exp.EvSm
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): **`segMi`** — `J10` (`smR`) → `m2inv := m1.modularInverseModPowerOfTwo(stk, m2, n)` →
`J11` (`miR`) (asm s62; twin of infra's arm64 `EvMi`)

`runMi` spills `z3` and pushes `miR`; `miPre` gives `ModInv.PreQ` (window `[sp - 8 - (232 + kc), sp + 64)`, reserve
level `lvl4 + D n`); the callee is a stack user (`stepC` with destination `m1`'s array, `StackBackL` / `ResSep` from
`ModInv.PostQ`). `m2`, `z2`, `z`, `z3` are apart from `m1` and survive; `m2inv` is located (`LN.of_sm`) and apart from
them (`apart_res`). Budget: `PostQ`'s `B − (cost + stkR H M) + stkR H M' ≤ b'` with `stkR ≤ stkRes` (`bud_q`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

theorem bud_q {rk b1 c sr rk' x y b2 : Nat} (h1 : rk ≤ b1) (h2 : c + sr + rk' ≤ rk) (h3 : x ≤ sr)
    (h4 : b1 - (c + x) + y ≤ b2) : rk' ≤ b2 := by omega

theorem bud_q0 {rk b1 c sr rk' : Nat} (h1 : rk ≤ b1) (h2 : c + sr + rk' ≤ rk) : c + sr ≤ b1 := by omega

/-- a slot read through `runMi`'s frame (push + `z3` spills) -/
theorem mi_own {sp : Nat} {M0 M : Memory} (hsp : 8 ≤ sp)
    (hF : MemFrame M0 M [(sp - 8, sp), (sp + 0x90, sp + 0xa0), (sp + 0x100, sp + 0x108)]) (o : Nat)
    (h : (0xa0 ≤ o ∧ o + 8 ≤ 0x100) ∨ 0x108 ≤ o ∨ o + 8 ≤ 0x90) : M.readLE (sp + o) 8 = M0.readLE (sp + o) 8 :=
  hF.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; omega)

/-- a slot read through a callee with `above = 72` at `RSP = sp - 8` -/
theorem mi_kc {sp : Nat} {M M' : Memory} (hsp : 8 ≤ sp)
    (hkc : ∀ a k, sp - 8 + 72 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) (o : Nat)
    (h1 : 0x40 ≤ o) (h2 : o + 8 ≤ 0x1b8) : M'.readLE (sp + o) 8 = M.readLE (sp + o) 8 :=
  hkc _ _ (by omega) (by omega)

/-- the `ESl` slots through both -/
theorem mi_slot {sp : Nat} {M0 M M' : Memory} (hsp : 8 ≤ sp)
    (hF : MemFrame M0 M [(sp - 8, sp), (sp + 0x90, sp + 0xa0), (sp + 0x100, sp + 0x108)])
    (hkc : ∀ a k, sp - 8 + 72 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) :
    ∀ a k, SlotR sp a k → M'.readLE a k = M0.readLE a k := fun a k ha => by
  simp only [SlotR] at ha
  rw [hkc a k (by omega) (by omega)]
  exact hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J10` → `J11`** (see the module doc) -/
theorem segMi {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {kc : Nat}
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} (hE : MiEns impl R kc sqrC mulC) (hK : 232 + kc ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hopA : Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hs16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → lvl4 s st mp ml l1 l2 + 8 * ModInv.NW (nE s mp ml) + 72 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml →
      ModInv.cost sqrC mulC l2 (nE s mp ml) + stkRes (lvl4 s st mp ml l1 l2 + ModInv.D (nE s mp ml)) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K11 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 : Nat),
      J11 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 : Nat}
    (h : J10 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hstw := hP.stkF.1
  unfold Apart at hstw
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
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
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hb0 : S.mem.readLE (sp + 0xb0) 8 = nE s mp ml := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h198 : S.mem.readLE (sp + 0x198) 8 = st := h.jx.esl.2.2.2.2.2.2.2.2.1
  have hs16' := hs16 l1 l2 hl1 hl2
  have hrk' := hrk l1 l2 hl1 hl2
  refine runMi ret0 Q sp st p1 l1 c1 q l2 (a2 ml (nE s mp ml)) (nE s mp ml) p3 l3 c3 S.mem hacc0 hsp8 (by omega)
    h.s118 h.sc8 h.sd0 h198 h.s110 h.sb8 h.sc0 hb0 h.p364
    (by have := h.z3.2.1; have := h.z3.1.1; omega) (by have := h.z3.1.1; omega) S h.pc h.jx.esp rfl h.r0 h.r3 h.r1 ?_
  have hspl : sp < 2 ^ 64 := by omega
  have hc1n : c1 ≠ 0 := by have := h.c1p; omega
  intro S2 M2 f0 f4 fm hF hrg frd r100 r90 r98 r0 r3 r1 r7 r6 r8 r9 r10 r5 r14 rfs rx15 rdf
  -- the spills and the push: `WC` and the locals at `M2`
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have kF : ∀ a, (a + 8 ≤ sp - 8 ∨ sp ≤ a) → (a + 8 ≤ sp + 0x90 ∨ sp + 0xa0 ≤ a) →
      (a + 8 ≤ sp + 0x100 ∨ sp + 0x108 ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 h3 =>
    hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hhd : HdrEq st S.mem M2 := by
    refine ⟨?_, kF _ (by omega) (by omega) (by omega), kF _ (by omega) (by omega) (by omega)⟩
    have := kF (st + 0) (by omega) (by omega) (by omega); simpa using this
  have hm1 := hown _ _ _ _ h.m1
  have hm2 := hown _ _ _ _ h.m2
  have hz2 := hown _ _ _ _ h.z2
  have hz3 := hown _ _ _ _ h.z3
  have hzs := LZ.frm hP hw (LiveExt.refl R L1) hF.accessible hhd (d := 0) (n := 0)
    (fun a k _ hw0 _ => hF.readLE a k (by
      unfold Apart at hw0; simp only [outside_cons, outside_nil, and_true]; omega)) h.zs
    (fun _ => by unfold Apart; omega)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  have hlen2 : stLen M2 st = lvl4 s st mp ml l1 l2 := hw2.len
  -- the call
  have hpre := miPre hP hopA hw2 hK tsp tg tfs fm (sqrC := sqrC) (mulC := mulC)
    hm1 h.c1p hp1 hm2 hl20 (by omega) hodd h.ap (by omega) (by omega) hs16' (bud_q0 hb1 hrk')
  have hS := Ensures.toSummaryIn (hE (lvl4 s st mp ml l1 l2 + ModInv.D (nE s mp ml)) b1 L1 p1 l1 c1 st q l2
      (a2 ml (nE s mp ml)) (nE s mp ml))
    (A64.noExit_restrict64 hap LibW.names) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap libW_sub)
  rw [modInv_a] at hS
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, hpre⟩
    (fun s' hr hq hrg' => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap libW_nf 1125 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0, r3, r1, r7, r6, r8, r9, r10, trivial⟩
  obtain ⟨⟨e4, -, e14, ex15⟩, hq⟩ := hq
  obtain ⟨efs, edf, p4, l4, c4, g0, g3, g1, hv, hN, hlc, hc40, L2, b2, hx, hb, hinv, hlv, hor, hsb, hF', hLF, hrs⟩ :=
    hq
  simp only [win, tsp, ModInv.K, ModInv.A] at hF'
  rw [fm] at hF' hLF hrg' hv hsb hrs hb
  rw [hm2.2.2.1] at hv
  rw [tg] at hinv
  have hloc1 := (hm1.1.2.2 h.c1p).1
  obtain ⟨dw, -, -, -⟩ := Loc.ap hP hloc1
  obtain ⟨hw', hkc, hkeep⟩ := stepC hP hw2 (Loc.sub hloc1) (Loc.subL hloc1) dw (stk := 232 + kc)
    (above := 72) hK (by decide) hF' hLF hrg' hx hinv hsb
  have hm2' := hkeep _ _ _ _ hm2 fun _ => h.ap
  have hz2' := hkeep _ _ _ _ hz2 h.wa1
  have hz3' := hkeep _ _ _ _ hz3 h.ta1
  have hzs' := LZ.step hP hw2 (stk := 232 + kc) (above := 72) hK (by decide) hF' hLF hx hsb hzs h.Za1
  have hp4 : p4 < 2 ^ 64 := by rw [← g0]; exact BitVec.isLt _
  have hmi := LN.of_sm hP hw2 hm1 hv hN hlc hc40 hlv hor hx hsb hrs
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by
    rw [e4, f4]; exact bv_add8 hsp8 hspl
  have hjx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s s' L2 b2 (lvl4 s st mp ml l1 l2) rk' :=
    ⟨hS4, e14.trans (r14.trans h.jx.e14), by rw [efs, rfs]; exact h.jx.efs, ex15.trans (rx15.trans h.jx.ex15),
      edf.trans (rdf.trans h.jx.edf), hw',
      h.jx.esl.keep (mi_slot hsp8 hF hkc),
      bud_q hb1 hrk' (stkR_le _ M2 st) hb⟩
  exact K11 s' L2 b2 l1 q l2 pw lw cw pZ cZ p3 l3 c3 p4 l4 c4 ⟨hjx, by rw [hr, retAddrOf_eq, tsp, fm, frd], hl1,
    bv_of_toNat g0, bv_of_toNat g3, bv_of_toNat g1,
    by rw [mi_kc hsp8 hkc 0x110 (by decide) (by decide), mi_own hsp8 hF 0x110 (by decide)]; exact h.s110,
    by rw [mi_kc hsp8 hkc 0xb8 (by decide) (by decide), mi_own hsp8 hF 0xb8 (by decide)]; exact h.sb8,
    by rw [mi_kc hsp8 hkc 0xc0 (by decide) (by decide), mi_own hsp8 hF 0xc0 (by decide)]; exact h.sc0,
    by rw [mi_kc hsp8 hkc 0xf8 (by decide) (by decide), mi_own hsp8 hF 0xf8 (by decide)]; exact h.sf8,
    by rw [mi_kc hsp8 hkc 0x80 (by decide) (by decide), mi_own hsp8 hF 0x80 (by decide)]; exact h.s80,
    by rw [mi_kc hsp8 hkc 0x88 (by decide) (by decide), mi_own hsp8 hF 0x88 (by decide)]; exact h.s88,
    by rw [mi_kc hsp8 hkc 0x108 (by decide) (by decide), mi_own hsp8 hF 0x108 (by decide)]; exact h.s108,
    by rw [mi_kc hsp8 hkc 0xa0 (by decide) (by decide), mi_own hsp8 hF 0xa0 (by decide)]; exact h.sa0,
    by rw [mi_kc hsp8 hkc 0xa8 (by decide) (by decide), mi_own hsp8 hF 0xa8 (by decide)]; exact h.sa8,
    by rw [mi_kc hsp8 hkc 0x100 (by decide) (by decide)]; exact r100,
    by rw [mi_kc hsp8 hkc 0x90 (by decide) (by decide)]; exact r90,
    by rw [mi_kc hsp8 hkc 0x98 (by decide) (by decide)]; exact r98,
    hm2', hz2', h.pw64, h.z2e, h.wa2, hzs', h.pZ64, h.Ze, h.Za2, h.Zz2, hz3', h.p364, h.z3e, h.ta2, h.tw, h.tZ, hmi, hp4,
    EL.of_res (fun e => absurd e hc1n) hw2.le hor,
    apart_res hor (h.m2.1.2.1 ha2).2.1 (fun _ => h.ap.symm),
    fun c0 cw0 => apart_res hor (h.z2.1.2.1 cw0).2.1 (fun _ => (h.wa1 cw0).symm) c0,
    fun c0 cZ0 => apart_res hor (h.zs.2.1 cZ0).2.1 (fun _ => (h.Za1 cZ0).symm) c0,
    fun c0 c30 => apart_res hor (h.z3.1.2.1 c30).2.1 (fun _ => (h.ta1 c30).symm) c0⟩

end

end FvModexp.Amd64.ExpEven
