import FvModexp.Proofs.Arm64.Exp.EvJ13
import FvModexp.Proofs.Arm64.Exp.EvTrD
import FvModexp.Proofs.Arm64.Exp.EvMulP
import FvModexp.Proofs.Arm64.Exp.EvSm

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): **`segTr`** — `J12` (`mul1R`) → `z2 = z2.trunc(z2, n)` → `J13` (`trR`) (agent infra)

`runTr`: `R3..R5 = t` (`X0..X2`), `R6 = n` (`184`), `CALL nat.trunc`. Premise `TrHyp0` (asm's `Trunc.Hyp0`, window
`4208 / 64`); `z = x = t`, so `trunc` reuses `t`'s array (`need = min(len t, ⌈n/64⌉) ≤ cap t`); a non-stack callee
(`frm_dst`, possibly EMPTY `t`); `m2`, `z`, `z3` survive.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mul1R` → `nat.trunc`'s entry -/
theorem runTr {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp n : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 false = true)
    (h184 : M.readLE (sp + 184) 8 = n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mul1R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1786000 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 0 →
      S'.regs 4 = S.regs 1 → S'.regs 5 = S.regs 2 → S'.regs 6 = BitVec.ofNat 64 n →
      S'.regs 30 = BitVec.ofNat 64 trR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
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
  janus_run [h184, hacc, hal] until [1786000]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

theorem trunc_a : segAddr Extracted.program Trunc.fn = 1786000 := by decide

theorem vT_lt (s : State) (xp xl yp yl mp ml : Nat) :
    vT s xp xl yp yl mp ml < 2 ^ (nE s mp ml + nE s mp ml) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' (Exp.subMod2N_spec _ _ _).1 (mi_lt _ _)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J12` → `J13`** (see the module doc) -/
theorem segTr {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    (htr : TrHyp0 impl R ns 4208 64)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    {rk rk' : Nat} (hrk : ∀ k, k ≤ 2 * ml → makeCost k + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K13 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lu ct : Nat),
      J13 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lu ct →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat}
    (h : J12 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hKs := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hgN : (S.regs 28).toNat = g := by rw [h.jx.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hacc : S.mem.accessible (sp + 128) 320 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  have hlt2 : lt ≤ 2 * ml := nlen_bd' h.t.2.2.2 (by
    rw [h.t.2.2.1]
    exact Nat.lt_of_lt_of_le (vT_lt _ _ _ _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hct := h.t.1.1
  have hltc := h.t.2.1
  have hneed : truncNeed lt (nE s mp ml) ≤ lt := Nat.min_le_left _ _
  refine runTr ret0 Q sp (nE s mp ml) S.mem hal hsp2 hacc h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 S h.pc
    h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r30 r18 r28 r29
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  have hgN' : (S'.regs 28).toNat = g := by rw [r28]; exact hgN
  have hfsp := fsp.trans h.jx.esp
  have hf28 := r28.trans h.jx.e28
  have hce := CallW.callEnv_of (hw.cenv hP) hfsp hf28 fm (stk := 4208) (above := 64) (by omega) (by decide)
  have hwr := DL.wr hP h.t.1 hsN' hgN' fm (stk := 4208) (above := 64) (by omega) (by omega)
  have hrd := LN.rd0 hP h.t hsN' fm (stk := 4208) (above := 64) (by omega) (by omega)
  have hS := CallNE.hypSum hap hns (htr b1 L1 (BitVec.ofNat 64 pt) (BitVec.ofNat 64 lt) (BitVec.ofNat 64 ct)
    (BitVec.ofNat 64 pt) (BitVec.ofNat 64 lt) (BitVec.ofNat 64 ct) (BitVec.ofNat 64 (nE s mp ml)))
  have t1 := LibCalls.tN h.pt64
  have t2 := LibCalls.tN (show lt < 2 ^ 64 by omega)
  have t3 := LibCalls.tN (show ct < 2 ^ 64 by omega)
  have t4 := LibCalls.tN (show nE s mp ml < 2 ^ 64 by omega)
  refine ReachesRet.call_regions hS (by rw [f0, trunc_a]) ⟨?_, ?_, ?_⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [trR]; omega)]
    exact ra_ev hap hnf 193 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0.trans h.r0, r1.trans h.r1, r2.trans h.r2, r3.trans h.r0, r4.trans h.r1, r5.trans h.r2, r6, trivial⟩
  · rw [t1, t2, t3, t4]
    refine ⟨⟨hce, hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hltc, hwr,
      hrd, by omega, by omega, Or.inl rfl, bud_pre hb1 (hrk _ (by omega)), by rw [hgN', fm]; exact hw.inv⟩,
      Or.inl (by rw [fm]; exact h.t.2.2.2), Or.inl rfl, fun _ => rfl⟩
  · simp only [t1, t3, t2, t4] at hq
    obtain ⟨p', l', c', g0, g1, g2, L2, b2, ⟨hv, hN, hlc, hc40, hlv, hke, -⟩, -, ⟨hx, hb, hinv⟩, hF, hLF⟩ := hq
    obtain ⟨rfl, rfl⟩ := hke (by omega)
    simp only [winA, hsN'] at hF
    rw [fm] at hF hLF hrg hv
    rw [h.t.2.2.1] at hv
    rw [hgN'] at hinv
    obtain ⟨qd, kd, hds, hdl, hdw, hF', hLF', hsb, ehd, hapd⟩ :=
      frm_dst hP hw h.t hx (stk := 4208) (above := 64) (by omega) (by omega) hF hLF
    obtain ⟨hw', hk, hkeep⟩ := stepC0 hP hw hds hdl hdw (stk := 4208) (above := 64) (by omega) (by omega) hF' hLF'
      hrg hx hinv hsb
    have hjx := h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw' hk (by omega)
      (bud_step hb1 (hrk _ (by omega)) hb)
    have hm2' := hkeep _ _ _ _ h.m2 fun c0 => hapd _ _ c0 fun ct0 => (h.tq ct0).symm
    have hz3' := hkeep _ _ _ _ h.z3 fun c0 => hapd _ _ c0 fun ct0 => (h.t3 ct0 c0).symm
    have hzs' := LZ.step hP hw (stk := 4208) (above := 64) (by omega) (by omega) hF' hLF' hx hsb h.zs
      fun c0 => hapd _ _ c0 fun ct0 => (h.tz ct0 c0).symm
    have ht := LN.of_sm hP hw h.t hv hN hlc hc40 hlv (Or.inl ⟨rfl, rfl⟩) hx hsb (fun _ hne => absurd ehd hne)
    have k : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 448 → s'.mem.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 => by
      rw [hk a 8 (Or.inr ⟨h1, h2⟩)]
    exact K13 s' L2 b2 l1 q l2 lw pZ cZ p3 l3 c3 p' l' c' ⟨hjx, hr.trans r30, h.l1m,
      g0, g1, g2,
      by rw [k _ (by omega) (by omega)]; exact h.s280, by rw [k _ (by omega) (by omega)]; exact h.s192,
      by rw [k _ (by omega) (by omega)]; exact h.s200, by rw [k _ (by omega) (by omega)]; exact h.s272,
      by rw [k _ (by omega) (by omega)]; exact h.s168, by rw [k _ (by omega) (by omega)]; exact h.s176,
      by rw [k _ (by omega) (by omega)]; exact h.s264, by rw [k _ (by omega) (by omega)]; exact h.s152,
      by rw [k _ (by omega) (by omega)]; exact h.s160,
      hm2', hzs', h.pZ64, h.Ze, h.Za2, hz3', h.p364, h.z3e, h.ta2, h.tZ, ht, h.pt64, h.te, h.tq, h.tz, h.t3⟩

end

end FvModexp.Arm64.ExpEven
