import FvModexp.Proofs.Arm64.Nat.DivLargeDRR

/-!
# `divLarge` (arm64): `n ≥ divRecursiveThreshold`, from `joinQ` over `clear(q)` (`memclr`) to `divRecursiveStep`

`dr2`: after `memclr` returns (`fn + 0x3c4`), the reloads to the call (`dr3`). `dr`: from `joinQ` to `memclr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `clear(q)`: reloads, then `divRecursiveStep`'s call (`dr3`) -/
theorem dr2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
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
    (k : ∀ L2 b2 w2 c2 T, AtD R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P
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

end FvModexp.Arm64.DivLarge
