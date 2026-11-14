import FvModexp.Proofs.Amd64.Exp.EvJ
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `m2 = stk.nat(ml - n/64)` (nat.go:810), `J2` → `J3` (asm s57; twin of infra's arm64 `EvN2`)

`runN2`: `lshR` → `(*stack).nat`'s entry (`m1` spilled to `0x118/0xc8/0xd0`, `AX = st` from `0x198`, `BX = a2` from
`0xd8`, return address `nat2R` pushed). `segN2`: the call, `m1` kept, the scratch `m2` apart from `m1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the frame of `runN2` -/
@[reducible] def FN2 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0xc8, sp + 0xd8), (sp + 0x118, sp + 0x120)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `lshR` → `(*stack).nat`'s entry -/
theorem runN2 {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp st k p1 l1 c1 : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x1c0 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48)
    (h198 : M.readLE (sp + 0x198) 8 = st) (hd8 : M.readLE (sp + 0xd8) 8 = k)
    (hp1 : p1 < 2 ^ 64) (hl1 : l1 < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 lshR) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 p1) (h3 : S.regs 3 = BitVec.ofNat 64 l1) (h1 : S.regs 1 = BitVec.ofNat 64 c1)
    (KN : ∀ (S' : State) (M' : Memory), S'.rip = BitVec.ofNat 64 0x5e6480 → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FN2 sp) → M'.regions = M.regions → M'.readLE (sp - 8) 8 = nat2R →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 k →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → M'.readLE (sp + 0x118) 8 = p1 → M'.readLE (sp + 0xc8) 8 = l1 → M'.readLE (sp + 0xd0) 8 = c1 →
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
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xc8, sp + 0xd8)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x118, sp + 0x120)) (by simp) (by simp only; omega)
          (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | rfl | skip

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the frame `FN2` leaves the slots -/
theorem fn2_slot {M M' : Memory} (hF : MemFrame M M' (FN2 sp)) :
    ∀ a k, SlotR sp a k → M'.readLE a k = M.readLE a k := fun a k ha => hF.readLE a k (by
  simp only [SlotR] at ha; simp only [FN2, outside_cons, outside_nil, and_true]; omega)

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J2` → `J3`** (see the module doc) -/
theorem segN2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 0x7f)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    (hl16 : stLen s.mem st + StackNat.rnd (a1 (nE s mp ml)) + a2 ml (nE s mp ml) + 3 ≤ 2 ^ 16)
    {rk rk' : Nat}
    (hrk : stackNatCost (stLen s.mem st + StackNat.rnd (a1 (nE s mp ml))) (a2 ml (nE s mp ml)) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K3 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q : Nat),
      J3 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 : Nat}
    (h : J2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hml := hP.2.2.2.2.2.1
  have ha2 : 0 < a2 ml (nE s mp ml) ∧ a2 ml (nE s mp ml) ≤ 128 := by simp only [a2]; omega
  have ha40 : a2 ml (nE s mp ml) < 2 ^ 40 := Nat.lt_of_le_of_lt ha2.2 (by decide)
  have hsp8 : 8 ≤ sp := by omega
  have hw := h.jx.wc
  have hm1 := h.m1
  have hc1 := h.c1p
  have hb1 := h.jx.bud
  have hp1 : p1 + 8 * c1 ≤ 2 ^ 48 := (hm1.1.2.1 hc1).2.2.2
  have hc40 : c1 < 2 ^ 40 := hm1.1.1
  have hl1 : l1 ≤ c1 := hm1.2.1
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  refine runN2 ret0 Q sp st (a2 ml (nE s mp ml)) p1 l1 c1 S.mem hacc0 (by omega) (by omega)
    h.jx.esl.2.2.2.2.2.2.2.2.1 h.sd8 (by omega) (by omega) (by omega) S h.pc h.jx.esp rfl h.r0 h.r3 h.r1 ?_
  intro S2 M2 f0 f4 fm hF hrg frd f3 fk f5 f14 ffs fx fdf r118 rc8 rd0
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (fun q hq => by
    simp only [FN2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have hm1' := hown _ _ _ _ hm1
  have hesl := h.jx.esl.keep (fn2_slot hF)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [f14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [ffs]; exact h.jx.efs
  have hpre := snPre (stk := stkN) (above := aboveN) (n := a2 ml (nE s mp ml)) hP hw2 hkN (by omega) tsp tg tfs fm
    (by omega) (by omega) (bud_pre hb1 hrk)
  refine snCallE hap hns hsn (ra := nat2R) (ra_ev hap hnf 338 (by decide)) S2 (by rw [f0, stkNat_a])
    (by rw [tsp, fm, frd]) (by have := hP.stk0.2.2.2.1; omega) (by omega) f3 fk
    (by rw [fx]; exact h.jx.ex15) (by rw [fdf]; exact h.jx.edf) hpre ?_
  intro s' g1 g2 g3 g4 g5 g6 hpost
  obtain ⟨L2, b2, hb2, hw3, hscE, hz0, hz1, hz2, hfs3, hdf3, hFn, hscC, hLFn, hx, harr⟩ :=
    WC.stkNat hP hw2 hkN (by omega) tsp tg fm (g6.trans (by rw [fm])) ha2.1 hpost
  have hlc := hw2.sok.2.2.2.2.2.1
  have hm1'' := LN.stkN hP hkN (by omega) hFn hLFn hx hlc (by rw [hw2.len, hw3.len]; omega) harr hm1'
  have hkc := keepC hP hw2 (zs := []) (by simpa only [List.append_nil] using hFn) hkN (by omega)
    (fun _ _ _ _ => by simp only [outside_nil])
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by rw [g2, f4]; exact bv_add8 (by omega) (by omega)
  refine K3 s' L2 b2 p1 l1 c1 _ ⟨⟨hS4, by rw [g4, f14]; exact h.jx.e14, by rw [hfs3, ffs]; exact h.jx.efs,
      by rw [g5, fx]; exact h.jx.ex15, by rw [hdf3, fdf]; exact h.jx.edf, hw3,
      hesl.keep (kc_slot hsp8 haN hkc),
      bud_step hb1 hrk hb2⟩, g1, hz0, hz1, hz2, ?_, ?_, ?_, hm1'', hc1,
    DL.of_scr hw3 hscE rfl lvl2_ge ha40,
    Scr.apartLN hscC hlc hm1' hc1⟩
  · rw [kc_at hsp8 haN hkc 0x118 8 (by decide) (by decide)]; exact r118
  · rw [kc_at hsp8 haN hkc 0xc8 8 (by decide) (by decide)]; exact rc8
  · rw [kc_at hsp8 haN hkc 0xd0 8 (by decide) (by decide)]; exact rd0

end

end FvModexp.Amd64.ExpEven
