import FvModexp.Proofs.Arm64.NatQ.DivLargeDRR

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivLargeDRM.lean, TIGHT COSTS, asm s38)
# `divLarge` (arm64): `n ≥ divRecursiveThreshold`, from `joinQ` over `clear(q)` (`memclr`) to `divRecursiveStep`

`dr2`: after `memclr` returns (`fn + 0x3c4`), the reloads to the call (`dr3`). `dr`: from `joinQ` to `memclr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `clear(q)`: reloads, then `divRecursiveStep`'s call (`dr3`) -/
theorem dr2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S)
    (Zm : Memory) (hZ : MemFrame S.mem Zm (scrB s))
    (z0 : Zm.readLE (s.sp.toNat - 64) 8 = qp) (z1 : Zm.readLE (s.sp.toNat - 56) 8 = il - vl + 1)
    (z2 : Zm.readLE (s.sp.toNat - 48) 8 = qc) (z3 : Zm.readLE (s.sp.toNat - 184) 8 = qc)
    (z4 : Zm.readLE (s.sp.toNat - 200) 8 = il - vl + 1) (z5 : Zm.readLE (s.sp.toNat - 112) 8 = qp)
    (m : Memory) (hMF : MemFrame Zm m (R.rt ++ [(s.sp.toNat - 304 - 4096, s.sp.toNat - 304 - 8),
      (s.sp.toNat - 304 + 8, s.sp.toNat - 304 + 8 + 8 * 2)] ++ [(qp, qp + 8 * (il - vl + 1))]))
    (hLF : LiveFrame Zm m Lq [(qp, qp + 8 * (il - vl + 1))]) (hinv : R.inv bq Lq (s.regs 28).toNat (view R.rt Lq m))
    (hzero : Mem.Zeroed m qp (8 * (il - vl + 1)))
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x3c4)) (hsp : T.sp = s.sp - 304#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 312#64) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = m)
    (hreg : m.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b H L (costQ dc il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hMU := hS.mem
  have hM := hMU.mem
  have hqcap := hS.qa.cap
  -- reads of frame slots at `m`
  have rdm : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat + 112 → m.readLE a 8 = Zm.readLE a 8 := fun a h1 h2 =>
    hMF.readLE _ _ (by
      have hqw := hS.qa.pw
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have rdz : ∀ a, Outside a 8 (scrB s) → Zm.readLE a 8 = S.mem.readLE a 8 := fun a h => hZ.readLE a 8 h
  have so : ∀ a, (s.sp.toNat - 192 ≤ a ∧ a + 8 ≤ s.sp.toNat - 184) ∨ (s.sp.toNat - 176 ≤ a ∧ a + 8 ≤ s.sp.toNat - 144) ∨
      (s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 88) ∨ (s.sp.toNat - 40 ≤ a ∧ a + 8 ≤ s.sp.toNat + 112) →
      Outside a 8 (scrB s) := by
    intro a h; simp only [scrB, outside_cons, outside_nil, and_true]; omega
  have r1 : m.readLE (s.sp.toNat - 96) 8 = t := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hM.vt
  have r2 : m.readLE (s.sp.toNat - 160) 8 = vl := by
    rw [rdm _ (by omega) (by omega), rdz _ (so _ (by omega))]; exact hM.vn1
  have r3 : m.readLE (s.sp.toNat - 152) 8 = vl := by
    rw [rdm _ (by omega) (by omega), rdz _ (so _ (by omega))]; exact hM.vn2
  have r4 : m.readLE (s.sp.toNat - 176) 8 = C := by
    rw [rdm _ (by omega) (by omega), rdz _ (so _ (by omega))]; exact hMU.sC
  have r5 : m.readLE (s.sp.toNat - 192) 8 = il + 1 := by
    rw [rdm _ (by omega) (by omega), rdz _ (so _ (by omega))]; exact hMU.sL
  have r6 : m.readLE (s.sp.toNat - 104) 8 = P := by
    rw [rdm _ (by omega) (by omega), rdz _ (so _ (by omega))]; exact hMU.sP
  have r7 : m.readLE (s.sp.toNat - 184) 8 = qc := by rw [rdm _ (by omega) (by omega)]; exact z3
  have r8 : m.readLE (s.sp.toNat - 200) 8 = il - vl + 1 := by rw [rdm _ (by omega) (by omega)]; exact z4
  have r9 : m.readLE (s.sp.toNat - 112) 8 = qp := by rw [rdm _ (by omega) (by omega)]; exact z5
  have r10 : m.readLE (s.sp.toNat + 32) 8 = st := by
    rw [rdm _ (by omega) (by omega), rdz _ (so _ (by omega))]; exact hM.s4
  have q0 : m.readLE (s.sp.toNat - 64) 8 = qp := by rw [rdm _ (by omega) (by omega)]; exact z0
  have q1 : m.readLE (s.sp.toNat - 56) 8 = il - vl + 1 := by rw [rdm _ (by omega) (by omega)]; exact z1
  have q2 : m.readLE (s.sp.toNat - 48) 8 = qc := by rw [rdm _ (by omega) (by omega)]; exact z2
  -- frames from `joinQ`
  have hA : MemFrame S.mem m (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]) := (mfTrans hZ hMF).mono fun a n ho => by
    simp only [outside_append] at ho
    obtain ⟨⟨h1, h2⟩, h3⟩ := ho
    have h2' := h2
    simp only [scrB, outside_cons, outside_nil, and_true] at h2'
    simp only [outside_cons, outside_nil, and_true] at h3
    rw [outside_append]
    exact ⟨h2, by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨h1, by omega, by omega⟩, by omega⟩⟩
  have hAL : LiveFrame S.mem m Lq [(qp, qp + 8 * qc)] := ⟨fun a n hin ho => by
    simp only [outside_cons, outside_nil, and_true] at ho
    rw [hLF.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; omega)]
    refine hZ.readLE a n ?_
    have hLs := lsep_of hE hS.ext3
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩
  have hz : natVal m qp (il - vl + 1) = 0 := FvModexp.Expmc.readLE_zeroed hzero
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : m.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hMF.accessible, hZ.accessible, hM.fr.accessible]; exact hw
  subst hm
  janus_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] until [segAddr Extracted.program drsFn]
  refine dr3 impl hap R dc hD b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS _ rfl rfl
    ?g28 ?g29 ?g18 ?g30 ?g0 ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10 ?hA ?hAL ?q0 ?q1 ?q2 ?hreg ?hz ?hinv Q k
  case hA => exact hA
  case hAL => exact hAL
  case q0 => exact q0
  case q1 => exact q1
  case q2 => exact q2
  case hreg => exact hreg
  case hz => exact hz
  case hinv => exact hinv
  case g30 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl
  case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `n ≥ divRecursiveThreshold`: from `joinQ` (q stored, threshold loaded, `BLT` not taken, spills) to `memclr(q)`, then
`dr2` -/
theorem dr (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDivL.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (hv40 : 40 ≤ vl)
    (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b H L (costQ dc il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hMU := hS.mem
  have hM := hMU.mem
  have m1 := hM.s4
  obtain ⟨g1, g2⟩ := Mem.glob hE hM
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hSacc]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr3 := hS.r3; have hr4 := hS.r4; have hr5 := hS.r5
  have hr6 := hS.r6; have hr12 := hS.r12; have hr14 := hS.r14; have hr15 := hS.r15
  have hgw : 7147136 + 32 ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ 7147136 := by
    have := hE.pre.gl.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at this; exact this
  have hQ := hS.qa
  have hqcap := hQ.cap; have hq48 := hQ.p48; have hq40 := hQ.c40
  have hl3 := lsl3_ofNat (il - vl + 1) (by omega)
  have hne : (BitVec.ofNat 64 (il - vl + 1) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hga := hE.pre.ce.2.2.2.2.1
  unfold Apart at hga
  have e304 : (s.sp - 304#64).toNat = s.sp.toNat - 304 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsv := hE.pre.sv
  janus_run [m1, g1, hl3, hne] until [cA "runtime.memclrNoHeapPointers"]
  refine ReachesRet.call_regions (hmc Lq bq) rfl (mc_pre (dst := qp) (n := 8 * (il - vl + 1)) hE hS.ext3 _ rfl ?q28 ?qg
    ?qa ?l1 ?l2 ?qi ?q0 ?q1 (hsv.2.2.1 _ _ (by omega)) (by omega) ?dacc ?dh ?dw) ?qk
  case q28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case qg =>
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hMU.grd
  case qa => intro a n w; simp only [Memory.accessible_writeLE]; exact hSacc a n w
  case l1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
  case l2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
  case qi =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 200, s.sp.toNat - 40)]) (by janus_frame) (fun r hr => ?_) hM.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case q0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
  case q1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
  case dacc =>
    simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hQ.pacc (Nat.le_refl _) (by omega)
  case dh => exact hQ.pheld.sub (Nat.le_refl _) (by omega)
  case dw => have := hQ.pw; omega
  case qk =>
    intro T hT ⟨junk, f, v, m, ex, ep, hs, hMF, hLF, hinv, hz⟩ hrg
    subst hs
    simp only [calleeStack, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, e304, h28] at hMF hLF hz hinv
    rw [Nat.mod_eq_of_lt (show qp < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * (il - vl + 1) < 2 ^ 64 by omega)]
      at hMF hLF hz
    refine dr2 impl hap R dc hD b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS ?Zm ?hZ
      ?z0 ?z1 ?z2 ?z3 ?z4 ?z5 m ?hMF ?hLF hinv hz _ ?pc ?sp ?r28 ?r29 ?r18 rfl ?hreg Q k
    case hMF => exact hMF
    case hLF => exact hLF
    case hZ => simp only [scrB]; janus_frame
    case pc => rw [hT]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl
    case sp => rfl
    case r28 =>
      simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, true_or, or_true, if_true]
    case r29 =>
      simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29, true_or, or_true, if_true]
    case r18 =>
      simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18, true_or, or_true, if_true]
    case hreg => simp only [retStateX, Memory.regions_writeLE] at hrg ⊢; rw [hrg]; exact hS.reg
    all_goals
      simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Memory.readLE_writeLE_of_disjoint, Nat.reducePow]
      omega

end FvModexp.Arm64.Q.DivLarge
