import FvModexp.Proofs.Amd64.Exp.EvJ2
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `z2 = stk.nat(2·max(len m1, len m2))` (nat.go:821), `J6` → `J7` (asm s58; twin of infra's
arm64 `EvN4`)

`runN4`: `exp1R` → `(*stack).nat`'s entry (`z1` spilled to `0x100/0x90/0x98`, `AX = st` from `0x198`, `BX = 2·max`
from `0xd8`, return address `nat4R` pushed). `segN4`: the call, `m1`, `m2`, `z1` kept, the scratch `z2` apart from
all three (from `z1`'s array only when it is non-empty).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the frame of `runN4` -/
@[reducible] def FN4 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x90, sp + 0xa0), (sp + 0x100, sp + 0x108)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `exp1R` → `(*stack).nat`'s entry -/
theorem runN4 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st k pz lz cz : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h198 : M.readLE (sp + 0x198) 8 = st) (hd8 : M.readLE (sp + 0xd8) 8 = k)
    (hp : pz < 2 ^ 64) (hl : lz < 2 ^ 64) (hc : cz < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 exp1R) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 pz) (h3 : S.regs 3 = BitVec.ofNat 64 lz) (h1 : S.regs 1 = BitVec.ofNat 64 cz)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 0x5e6480 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FN4 sp) → M'.regions = M.regions → M'.readLE (sp - 8) 8 = nat4R →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 k →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → M'.readLE (sp + 0x100) 8 = pz → M'.readLE (sp + 0x90) 8 = lz → M'.readLE (sp + 0x98) 8 = cz →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hs : M.readLE (sp + 0x198) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hk : M.readLE (sp + 0xd8) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize x5 : S.regs 5 = r5 at KN
  generalize x14 : S.regs 14 = r14 at KN
  generalize xf : S.fsBase = rf at KN
  generalize xx : S.xmm 15 = rx at KN
  generalize xd : S.df = rd at KN
  janus64_run [h198, hd8, e4] until [0x5e6480]
  refine KN _ _ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x90, sp + 0xa0)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x100, sp + 0x108)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | skip

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the frame `FN4` leaves the slots -/
theorem fn4_slot {M M' : Memory} (hF : MemFrame M M' (FN4 sp)) :
    ∀ a k, SlotR sp a k → M'.readLE a k = M.readLE a k := fun a k ha => hF.readLE a k (by
  simp only [SlotR] at ha; simp only [FN4, outside_cons, outside_nil, and_true]; omega)

/-- the frame `FN4` leaves `m1`'s, `m2`'s slots and `0xd8` -/
theorem fn4_m {M M' : Memory} (hsp : 8 ≤ sp) (hF : MemFrame M M' (FN4 sp)) :
    ∀ o, 0xb8 ≤ o → o + 8 ≤ 0xe0 ∨ 0x110 ≤ o ∧ o + 8 ≤ 0x120 → M'.readLE (sp + o) 8 = M.readLE (sp + o) 8 := by
  intro o h1 h2
  refine hF.readLE _ _ ?_
  simp only [FN4, outside_cons, outside_nil, and_true]; omega

theorem lvl4_ge {l1 l2 : Nat} : lvl3 s st mp ml l1 l2 + 2 * max l1 l2 ≤ lvl4 s st mp ml l1 l2 := by
  have := rnd_ge (2 * max l1 l2); simp only [lvl4]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J6` → `J7`** (see the module doc) -/
theorem segN4 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 0x7f)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hl16 : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → lvl3 s st mp ml l1 l2 + 2 * ml + 3 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : ∀ l1 l2, l1 ≤ ml → l2 ≤ ml → stackNatCost (lvl3 s st mp ml l1 l2) (2 * max l1 l2) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K7 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz t : Nat),
      J7 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q l2 pz lz cz t →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz : Nat}
    (h : J6 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hml := hP.2.2.2.2.2.1
  have ha2 : 0 < a2 ml (nE s mp ml) ∧ a2 ml (nE s mp ml) ≤ ml := by simp only [a2]; omega
  have hsp8 : 8 ≤ sp := by omega
  have hw := h.jx.wc
  have hm1 := h.m1
  have hm2 := h.m2
  have hz := h.z1
  have hc1 := h.c1p
  have hb1 := h.jx.bud
  have hl1m : l1 ≤ ml := by
    have hv : natVal S.mem p1 l1 < 2 ^ (64 * ml) := by
      rw [hm1.2.2.1]; exact Nat.pow_lt_pow_right (by decide) hnl
    exact nlen_bd' hm1.2.2.2 hv
  have hl2m : l2 ≤ ml := Nat.le_trans hm2.2.1 ha2.2
  have hl1p : 0 < l1 := by
    rcases Nat.eq_zero_or_pos l1 with h0 | h0
    · have hv := hm1.2.2.1
      rw [h0, natVal_zero] at hv
      exact absurd hv.symm (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
    · exact h0
  have hmx1 : l1 ≤ max l1 l2 := Nat.le_max_left _ _
  have hmx3 : max l1 l2 ≤ ml := Nat.max_le.2 ⟨hl1m, hl2m⟩
  have hpos : 0 < 2 * max l1 l2 := by omega
  have hrk' := hrk l1 l2 hl1m hl2m
  have hl16' := hl16 l1 l2 hl1m hl2m
  have hcz : cz < 2 ^ 40 := hz.1.1
  have hlz : lz ≤ cz := hz.2.1
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  refine runN4 ret0 Q sp st (2 * max l1 l2) pz lz cz S.mem hacc0 (by omega) (by omega)
    h.jx.esl.2.2.2.2.2.2.2.2.1 h.sd8 h.pz64 (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r3 h.r1 ?_
  intro S2 M2 f0 f4 fm hF hrg frd f3 fk f5 f14 ffs fx fdf r100 r90 r98
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun q hq => by
    simp only [FN4, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have hm1' := hown _ _ _ _ hm1
  have hm2' := hown _ _ _ _ hm2
  have hz' := hown _ _ _ _ hz
  have em := fn4_m hsp8 hF
  have hesl := h.jx.esl.keep (fn4_slot hF)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [f14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [ffs]; exact h.jx.efs
  have hpre := snPre (stk := stkN) (above := aboveN) (n := 2 * max l1 l2) hP hw2 hkN (by omega) tsp tg tfs fm
    (by omega) (by omega) (bud_pre hb1 hrk')
  refine snCallE hap hns hsn (ra := nat4R) (ra_ev hap hnf 601 (by decide)) S2 (by rw [f0, stkNat_a])
    (by rw [tsp, fm, frd]) (by have := hP.stk0.2.2.2.1; omega) (by omega) f3 fk
    (by rw [fx]; exact h.jx.ex15) (by rw [fdf]; exact h.jx.edf) hpre ?_
  intro s' g1 g2 g3 g4 g5 g6 hpost
  obtain ⟨L2, b2, hb2, hw3, hscE, hz0, hz1, hz2, hfs3, hdf3, hFn, hscC, hLFn, hx, harr⟩ :=
    WC.stkNat hP hw2 hkN (by omega) tsp tg fm (g6.trans (by rw [fm])) hpos hpost
  have hlc := hw2.sok.2.2.2.2.2.1
  have hle : stLen M2 st ≤ stLen s'.mem st := by rw [hw2.len, hw3.len]; omega
  have kN := fun {p l c v : Nat} (hq : LN R L s.mem st M2 L1 p l c v) =>
    LN.stkN hP hkN (by omega) hFn hLFn hx hlc hle harr hq
  have hkc := keepC hP hw2 (zs := []) (by simpa only [List.append_nil] using hFn) hkN (by omega)
    (fun _ _ _ _ => by simp only [outside_nil])
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by rw [g2, f4]; exact bv_add8 (by omega) (by omega)
  have h40 : 2 * max l1 l2 < 2 ^ 40 := by omega
  refine K7 s' L2 b2 p1 l1 c1 q l2 pz lz cz _ ⟨⟨hS4, by rw [g4, f14]; exact h.jx.e14,
      by rw [hfs3, ffs]; exact h.jx.efs, by rw [g5, fx]; exact h.jx.ex15, by rw [hdf3, fdf]; exact h.jx.edf, hw3,
      hesl.keep (kc_slot hsp8 haN hkc),
      bud_step hb1 hrk' hb2⟩, g1, hz0, hz1, hz2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, kN hm1', hc1, kN hm2', h.ap,
    kN hz', h.pz64, h.z1e, h.za1, h.za2,
    DL.of_scr hw3 hscE rfl lvl4_ge h40,
    Scr.apartLN hscC hlc hm1' hc1, Scr.apartLN hscC hlc hm2' ha2.1, fun hc => Scr.apartLN hscC hlc hz' hc⟩
  · rw [kc_at hsp8 haN hkc 0x118 8 (by decide) (by decide), em 0x118 (by decide) (Or.inr (by decide))]
    exact h.s118
  · rw [kc_at hsp8 haN hkc 0xc8 8 (by decide) (by decide), em 0xc8 (by decide) (Or.inl (by decide))]; exact h.sc8
  · rw [kc_at hsp8 haN hkc 0xd0 8 (by decide) (by decide), em 0xd0 (by decide) (Or.inl (by decide))]; exact h.sd0
  · rw [kc_at hsp8 haN hkc 0x110 8 (by decide) (by decide), em 0x110 (by decide) (Or.inr (by decide))]
    exact h.s110
  · rw [kc_at hsp8 haN hkc 0xb8 8 (by decide) (by decide), em 0xb8 (by decide) (Or.inl (by decide))]; exact h.sb8
  · rw [kc_at hsp8 haN hkc 0xc0 8 (by decide) (by decide), em 0xc0 (by decide) (Or.inl (by decide))]; exact h.sc0
  · rw [kc_at hsp8 haN hkc 0xd8 8 (by decide) (by decide), em 0xd8 (by decide) (Or.inl (by decide))]; exact h.sd8
  · rw [kc_at hsp8 haN hkc 0x100 8 (by decide) (by decide)]; exact r100
  · rw [kc_at hsp8 haN hkc 0x90 8 (by decide) (by decide)]; exact r90
  · rw [kc_at hsp8 haN hkc 0x98 8 (by decide) (by decide)]; exact r98

end

end FvModexp.Amd64.ExpEven
