import FvModexp.Proofs.Amd64.Nat.DivLargeDRR

set_option autoImplicit false

/-!
# `divLarge` (amd64): `n ≥ divRecursiveThreshold`, from `joinQ` over `clear(q)` (`memclr`) to `divRecursiveStep`

`+0x58f`: `q` stored at `RSP - 64 … - 48`; `CMPQ divRecursiveThreshold, R11; JG` not taken (`n ≥ 40`); `TESTQ R9`
(`m + 1 ≠ 0`); spills `R13 = cap q` (`RSP - 192`), `R9 = m + 1` (`- 208`), `R15 = q.ptr` (`- 112`); `memclr(q, 8(m+1))`
(`CALL` at `+0x5d6`, return `+0x5db`). `dr`: joinQ → the return. `dr2`: reloads, `v = (t, vl, vl)` at `RSP' + 0 … + 16`,
args, `CALL divRecursiveStep` (`+0x642`) → `dr3`. `dr_mem`: the memory facts at the callee entry (pure).
Port of `Arm64/Nat/DivLargeDRM.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the memory at `divRecursiveStep`'s entry (pure): `Zm` = `AtJ`'s with `scrB` stores, `m` = after `memclr(q)`, `M2` =
with the stack args and the return address -/
theorem dr_mem {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S)
    {Zm m M2 : Memory} {cs : List (Nat × Nat)} (hZ : MemFrame S.mem Zm (scrB s))
    (hMF : MemFrame Zm m (R.rt ++ cs ++ [(qp, qp + 8 * (il - vl + 1))]))
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 41272 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 288)
    (hLF : LiveFrame Zm m Lq [(qp, qp + 8 * (il - vl + 1))]) (hinv : R.inv bq Lq (s.regs 14).toNat (view R.rt Lq m))
    (hzero : Mem.Zeroed m qp (8 * (il - vl + 1)))
    (hW : MemFrame m M2 [((s.regs 4).toNat - 312, (s.regs 4).toNat - 280)]) :
    MemFrame S.mem M2 (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]) ∧ LiveFrame S.mem M2 Lq [(qp, qp + 8 * qc)] ∧
      (∀ a n, (s.regs 4).toNat - 280 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → M2.readLE a n = Zm.readLE a n) ∧
      natVal M2 qp (il - vl + 1) = 0 ∧ R.inv bq Lq (s.regs 14).toNat (view R.rt Lq M2) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have hQ := hS.qa
  have hqcap := hQ.cap; have hqw := hQ.pw
  have hLs := lsep_of hE hS.ext3
  have hWo : ∀ a n, ((s.regs 4).toNat - 280 ≤ a ∨ a + n ≤ (s.regs 4).toNat - 312) → M2.readLE a n = m.readLE a n :=
    fun a n h => hW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (mfTrans (mfTrans hZ hMF) hW).mono fun a n ho => ?_
    simp only [outside_append] at ho
    obtain ⟨⟨h1, h2⟩, h3⟩ := ho
    have h2' := h2
    simp only [scrB, outside_cons, outside_nil, and_true] at h2'
    simp only [outside_cons, outside_nil, and_true] at h3
    simp only [outside_append]
    refine ⟨⟨h2, ⟨h1, outside_of_forall fun r hr => ?_⟩, by simp only [outside_cons, outside_nil, and_true]; omega⟩,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩
    have := hcs r hr; omega
  · refine ⟨fun a n hin ho => ?_⟩
    simp only [outside_cons, outside_nil, and_true] at ho
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    rw [hWo a n (by omega), hLF.readLE a n ⟨r, hr, i1, i2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hZ.readLE a n (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)
  · intro a n h1 h2
    rw [hWo a n (Or.inl h1)]
    refine hMF.readLE a n ?_
    rw [outside_append, outside_append]
    refine ⟨⟨hout.of_sub (by omega) (by omega), outside_of_forall fun r hr => ?_⟩, ?_⟩
    · have := hcs r hr; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
  · have hz := FvModexp.Expmc.readLE_zeroed hzero
    unfold natVal; rw [hWo _ _ (by omega)]; exact hz
  · refine RtInv.inv_frame' hW (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `clear(q)` (`+0x5db`): reloads, `v` stack args, `CALL divRecursiveStep`, then `dr3` -/
theorem dr2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hD : DrsHyp impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S)
    (Zm : Memory) (hZ : MemFrame S.mem Zm (scrB s))
    (z0 : Zm.readLE ((s.regs 4).toNat - 64) 8 = qp) (z1 : Zm.readLE ((s.regs 4).toNat - 56) 8 = il - vl + 1)
    (z2 : Zm.readLE ((s.regs 4).toNat - 48) 8 = qc) (z3 : Zm.readLE ((s.regs 4).toNat - 192) 8 = qc)
    (z4 : Zm.readLE ((s.regs 4).toNat - 208) 8 = il - vl + 1) (z5 : Zm.readLE ((s.regs 4).toNat - 112) 8 = qp)
    (m : Memory) {cs : List (Nat × Nat)} (hMF : MemFrame Zm m (R.rt ++ cs ++ [(qp, qp + 8 * (il - vl + 1))]))
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 41272 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 288)
    (hLF : LiveFrame Zm m Lq [(qp, qp + 8 * (il - vl + 1))]) (hinv : R.inv bq Lq (s.regs 14).toNat (view R.rt Lq m))
    (hzero : Mem.Zeroed m qp (8 * (il - vl + 1)))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x5db))
    (hsp : T.regs 4 = s.regs 4 - 304#64) (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14)
    (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0#128) (hdf : T.df = false) (hm : T.mem = m)
    (hreg : m.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hMU := hS.mem
  have hM := hMU.mem
  have hqw := hS.qa.pw; have hqcap := hS.qa.cap
  -- reads of frame slots at `m` (the `memclr` frame: `cs` below `RSP - 288`, `q` outside the window)
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have rdm : ∀ a, (s.regs 4).toNat - 280 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 → m.readLE a 8 = Zm.readLE a 8 :=
    fun a h1 h2 => hMF.readLE _ _ (by
      simp only [outside_append]
      refine ⟨⟨hout.of_sub (by omega) (by omega), outside_of_forall fun r hr => ?_⟩, ?_⟩
      · have := hcs r hr; omega
      · simp only [outside_cons, outside_nil, and_true]; omega)
  have r1 : m.readLE ((s.regs 4).toNat - 96) 8 = t := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hM.vt
  have r2 : m.readLE ((s.regs 4).toNat - 152) 8 = vl := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hM.vn2
  have r3 : m.readLE ((s.regs 4).toNat - 184) 8 = C := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hMU.sC
  have r4 : m.readLE ((s.regs 4).toNat - 200) 8 = il + 1 := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hMU.sL
  have r5 : m.readLE ((s.regs 4).toNat - 104) 8 = P := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hMU.sP
  have r6 : m.readLE ((s.regs 4).toNat - 160) 8 = vl := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hM.vn1
  have r7 : m.readLE ((s.regs 4).toNat - 208) 8 = il - vl + 1 := by rw [rdm _ (by omega) (by omega)]; exact z4
  have r8 : m.readLE ((s.regs 4).toNat - 192) 8 = qc := by rw [rdm _ (by omega) (by omega)]; exact z3
  have r9 : m.readLE ((s.regs 4).toNat - 112) 8 = qp := by rw [rdm _ (by omega) (by omega)]; exact z5
  have r10 : m.readLE ((s.regs 4).toNat + 80) 8 = st := by
    rw [rdm _ (by omega) (by omega), hZ.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)]
    exact hM.s4
  have hacc : m.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    obtain ⟨-, ⟨-, -, hw⟩, -⟩ := hE.pre.ce
    simp only [regSP] at hw
    rw [hMF.accessible, hZ.accessible, hM.fr.accessible]; exact hw
  have hc40 := hS.ua.c40; have hcap := hS.ua.cap; have hq48 := hS.qa.p48; have ht48 := hl.t48
  have hq40 := hS.qa.c40; have hp48 := hS.ua.p48; have hst48 := hl.st48
  subst hm
  janus64_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] until [segAddr Extracted.program drsFn]
  have hD4 := fun M2 (hW : MemFrame T.mem M2 [((s.regs 4).toNat - 312, (s.regs 4).toNat - 280)]) =>
    dr_mem hE hS hZ hMF hcs hLF hinv hzero hW
  refine dr3 impl hap R dc hD b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc hE S hS _
    ?gpc ?gsp ?grd ?g5 ?g14 ?gfs ?gx ?gdf ?g0 ?g3 ?g1 ?g7 ?g6 ?g8 ?g9 (hD4 _ ?W).1 (hD4 _ ?W).2.1
    ?q0 ?q1 ?q2 ?vS ?lS ?cS ?greg (hD4 _ ?W).2.2.2.1 (hD4 _ ?W).2.2.2.2 Q k
  case W => janus_frame
  case q0 => rw [(hD4 _ (by janus_frame)).2.2.1 _ _ (by omega) (by omega)]; exact z0
  case q1 => rw [(hD4 _ (by janus_frame)).2.2.1 _ _ (by omega) (by omega)]; exact z1
  case q2 => rw [(hD4 _ (by janus_frame)).2.2.1 _ _ (by omega) (by omega)]; exact z2
  case greg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hreg
  all_goals (try janus64_simp)
  all_goals first
    | exact h5 | exact h14 | exact hfs | exact hx15 | rfl | bv_omega
    | (simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Nat.reducePow]; omega)
    | skip

end FvModexp.Amd64.DivLarge
