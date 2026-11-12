import FvModexp.Proofs.Arm64.Nat.DivLargeMem

/-!
# `divLarge` (arm64): `u = u.make(len(uIn) + 1)` (natdiv.go:608), allocation path (`cap u < len uIn + 1`)

Store `v` (`SP - 96, -160, -152`); `CMP R4, R3; BLT` (`cap u < len uIn + 1`, signed) → allocation
`makeslice(Word, len uIn + 1, len uIn + 5)` (`len uIn ≠ 0`), else reuse `u`; the join stores `u` at `SP - 104, -192, -176`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges)
open FvModexp (Held.readLE2 liveFrame_of_frame)
open FvModexp.Arm64.DivBasic (LiveFrame.trans')

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the allocation path (`cap u < len uIn + 1`): `makeslice(Word, len uIn + 1, len uIn + 5)` -/
theorem mkA (impl : List Segment) (R : RtInv) (stkSN abSN : Nat) (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (hmk : MakesliceLiveContract (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (hpre : Pre R b L c zp zc st up uc ip il vp vl s)
    (P : State) (hP : AtNat st up uc ip il ic vp vl vc zp zc s P)
    (S2 : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hA : AfterNat R b L st vl s P S2 stkSN abSN L1 b1)
    (hz : uc < il + 1) (hb1 : makeCost (il + 1) ≤ b1) (Q : State → Prop)
    (k : ∀ S Lk bk P' C', AtU R b L zp zc st up uc ip il ic vp vl vc s (stW S2.mem st + 8 * stLen s.mem st)
      (stW S2.mem st) (stCap S2.mem st) L1 b1 Lk bk P' C' S → ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S2 Q := by
  have hE := env_of (S2 := S2.mem) hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow
    (fun a n v => by rw [hA.F2.accessible, hP.fr.accessible])
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hv2 := hl.v2; have hvil := hl.vil
  have hu40 := hpre.uo.1
  have p1 : S2.mem.readLE (s.sp.toNat + 56) 8 = uc := (rdS2 hpre hk1 hk2 hA _ _ (by omega) (by omega) (by omega)).trans hP.s7
  have p2 : S2.mem.readLE (s.sp.toNat - 136) 8 = il + 1 :=
    (rdS2 hpre hk1 hk2 hA _ _ (by omega) (by omega) (by omega)).trans hP.il1
  have p4 : S2.mem.readLE (s.sp.toNat + 72) 8 = il := (rdS2 hpre hk1 hk2 hA _ _ (by omega) (by omega) (by omega)).trans hP.s9
  obtain ⟨hal, hb', ha, hw⟩ := hpre.ce.2.1
  have hS2acc : ∀ a n v, S2.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hA.F2.accessible, hP.fr.accessible]
  have hwacc : S2.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hS2acc]; exact hw
  have hpc2 := hA.pc; have hsp2 := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hr0 := hA.r0; have hr1 := hA.r1; have hr2 := hA.r2
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  have hd := hpre.ce.2.2.1
  have hro := hpre.ce.2.2.2.2.2.2.2
  have hsv := hpre.sv
  have hiS : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have hiw := hl.iw; have hsi := hpre.si
    unfold Apart at hsi
    rw [Held.readLE2 (hpre.io.2.2.2.1.sub h1 h2) hA.F2 hA.LF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega),
      hP.fr.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
  have hil0 : (BitVec.ofNat 64 il = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hk1' : il + 1 ≠ 1 := by omega
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 41264) (41264 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, il + 1, il + 5] := hsv.1 _ _ _ (by omega)
  have hmcost : makeCost (il + 1) = allocCost (8 * (il + 1 + 4)) := by unfold makeCost makeCap; rw [if_neg hk1']
  have hbl := blockSize_le_allocCost (8 * (il + 1 + 4)) true
  have hbs : blockSize (8 * (il + 1 + 4)) true ≤ b1 := by omega
  have hinv2 := hA.inv
  have hga := hpre.ce.2.2.2.2.1
  have hgr := hpre.ce.2.2.2.2.2.1
  unfold Apart at hwt hga
  have hWw : Outside wordT 16 (stkWs s.mem st) := by
    have hstacc := hpre.sti.1.2.2.1
    refine outside_stkWs hpre (apart_of_data hd 1 (by decide) (by decide) hstacc) fun hc => ?_
    exact apart_of_data hd 1 (by decide) (by decide) (hpre.sti.1.2.2.2.2.1 hc).2.2.1
  have hWr : ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [hA.F2.readLE a n ?_, hP.fr.readLE a n ?_]
    · simp only [proWs, outside_cons, outside_nil, and_true]; omega
    · have h3 := hWw.of_sub h1 (show a + n ≤ wordT + 16 by omega)
      simp only [stkWs, outside_cons, outside_nil, and_true] at h3
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hty.of_sub h1 (by omega), by omega, by omega⟩, h3⟩
  have hgW : Outside ((s.regs 28).toNat + 16) 8 (stkWs s.mem st) := by
    refine outside_stkWs hpre (hpre.sti.2.2.1.symm) fun hc => ?_
    exact (hpre.sti.2.2.2 hc).2.symm
  have hgS : S2.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hA.F2.readLE _ _ ?_, hP.fr.readLE _ _ ?_]
    · simp only [proWs, outside_cons, outside_nil, and_true]; omega
    · simp only [outside_append, outside_cons, outside_nil, and_true]
      simp only [stkWs, outside_cons, outside_nil, and_true] at hgW
      exact ⟨⟨hgr, by omega, by omega⟩, hgW⟩
  obtain ⟨hg1, hg2, hg3⟩ := hpre.ce.1
  have hgacc : S2.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hS2acc]; exact hg2
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : S2.mem.readLE 2641088 8 = s.mem.readLE 2641088 8 := hWr _ _ (by omega) (by omega)
  have hT2 : S2.mem.readLE 2641096 8 = s.mem.readLE 2641096 8 := hWr _ _ (by omega) (by omega)
  have hTa : S2.mem.accessible 2641088 16 false = s.mem.accessible 2641088 16 false := hS2acc _ _ _
  have hLs1 := hl.lsep
  have hc1 := hE.c1len
  have hw1h : Held R L1 (stW S2.mem st) (8 * stCap S2.mem st) := (hA.ok.2.2.2.2.1 (by
    simp only [StackNat.rnd] at hc1; omega)).2.1
  janus_run [p1, p2, p4, hil0, hT1, hT2, hTa, hgS] until [joinU] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
  have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
  have hptr : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hS1 : MemFrame S2.mem ((((S2.mem.writeLE (s.sp.toNat - 96) 8 (stW S2.mem st + 8 * stLen s.mem st)).writeLE
      (s.sp.toNat - 160) 8 vl).writeLE (s.sp.toNat - 152) 8 vl).writeLE (s.sp.toNat - 176) 8 (il + 5))
      [(s.sp.toNat - 160, s.sp.toNat - 144), (s.sp.toNat - 120, s.sp.toNat - 88), (s.sp.toNat - 200, s.sp.toNat - 168)] := by
    janus_frame
  have hS3 : MemFrame m (((m.writeLE (s.sp.toNat - 176) 8 (il + 5)).writeLE (s.sp.toNat - 192) 8 (il + 1)).writeLE
      (s.sp.toNat - 104) 8 ptr.toNat) [(s.sp.toNat - 200, s.sp.toNat - 168), (s.sp.toNat - 104, s.sp.toNat - 96)] := by
    janus_frame
  have hMall := mfTrans hS1 (mfTrans hMF hS3)
  have hsl : ∀ a n, Outside a n (R.rt ++ slotsW s) →
      Outside a n ([(s.sp.toNat - 160, s.sp.toNat - 144), (s.sp.toNat - 120, s.sp.toNat - 88),
        (s.sp.toNat - 200, s.sp.toNat - 168)] ++ ((R.rt ++ [(s.sp.toNat - 304 - 4096, s.sp.toNat - 304 - 8),
        (s.sp.toNat - 304 + 8, s.sp.toNat - 304 + 8 + 24)]) ++
        [(s.sp.toNat - 200, s.sp.toNat - 168), (s.sp.toNat - 104, s.sp.toNat - 96)])) := by
    intro a n h
    simp only [slotsW, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨hrt, h1, h2, h3, h4, h5⟩ := h
    exact ⟨⟨h4, h5, h3⟩, ⟨hrt, by omega, by omega⟩, h3, by omega⟩
  have hM : MemFrame S2.mem (((m.writeLE (s.sp.toNat - 176) 8 (il + 5)).writeLE (s.sp.toNat - 192) 8 (il + 1)).writeLE
      (s.sp.toNat - 104) 8 ptr.toNat) (R.rt ++ slotsW s) := hMall.mono hsl
  have hLw : ∀ {m1 m2 : Memory} {ws : List (Nat × Nat)}, MemFrame m1 m2 ws →
      (∀ r ∈ ws, s.sp.toNat - 41264 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 112) → LiveFrame m1 m2 L1 [] := by
    intro m1 m2 ws h hws
    exact liveFrame_of_frame (rs := ws) (ws := []) (lo := s.sp.toNat - 41264) (hi := s.sp.toNat + 112)
      (by simpa using h) hl.lsep hws
  have hML : LiveFrame S2.mem (((m.writeLE (s.sp.toNat - 176) 8 (il + 5)).writeLE (s.sp.toNat - 192) 8 (il + 1)).writeLE
      (s.sp.toNat - 104) 8 ptr.toNat) L1 [] :=
    LiveFrame.trans' (LiveFrame.trans' (hLw hS1 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only <;> omega)) hLF)
      (hLw hS3 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega))
  have hblk : blockSize (8 * (il + 5)) true ≤ makeCost (il + 1) := by rw [hmcost]; exact hbl
  refine k _ (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (il + 5)) true)]) (b1 - blockSize (8 * (il + 5)) true)
    ptr.toNat (il + 1 + 4) ⟨?qpc, rfl, ?q28, ?q29, ?q18, ?q0, ?q1, ?q2, ?q3, ?q4, ?q5, ?qmem, ?qC, ?qL, ?qP, ?qua,
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, ?qis⟩
  case qpc => janus_simp
  case q28 => janus_simp
  case q29 => janus_simp
  case q18 => janus_simp
  case q0 => janus_simp; rw [Nat.mod_eq_of_lt (by have := hl.t48; omega)]
  case q1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q5 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case qmem =>
    refine mem_of_nat hE hk1 hk2 hP hA.F2 hA.LF2 rfl hA.len rfl (hM) hML ?_ ?_ ?_ ?_
    · rw [hS3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
        hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
      janus_simp; have := hl.t48; omega
    · rw [hS3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
        hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
      janus_simp
    · rw [hS3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
        hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
      janus_simp
    · refine RtInv.inv_frame' hS3 (fun r hr => ?_) hinv'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      left
      rcases hr with rfl | rfl <;> exact hout.of_sub (by dsimp only; omega) (by dsimp only; omega)
  case qC => janus_simp
  case qL => janus_simp
  case qP => janus_simp
  case qua =>
    refine uarr_alloc hE hz hAp hIn hle ?_ h8' (by omega) hw1h
    simp only [Memory.accessible_writeLE]; rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc
  case qis =>
    intro a n h1 h2
    have hiw := hl.iw
    rcases (hpre.io.2.2.2.1.sub h1 h2) with hi | ho
    · rw [hML.readLE a n (hE.ext.inRanges_old hi) (by simp)]; exact hiS a n h1 h2
    · rw [hM.readLE a n (by
        rw [outside_append]; exact ⟨ho, by simp only [slotsW, outside_cons, outside_nil, and_true]; omega⟩)]
      exact hiS a n h1 h2

end FvModexp.Arm64.DivLarge
