import FvModexp.Proofs.Arm64.Nat.DivLargeMem

/-!
# `divLarge` (arm64): `u = u.make(len(uIn) + 1)` (natdiv.go:608), from `stk.nat`'s return to `joinU`

Store `v` (`SP - 96, -160, -152`); `CMP R4, R3; BLT` (`cap u < len uIn + 1`, signed) → allocation
`makeslice(Word, len uIn + 1, len uIn + 5)` (`len uIn ≠ 0`), else reuse `u`; the join stores `u` at `SP - 104, -192, -176`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (outside_of_inRanges)
open FvModexp (Held.readLE2 liveFrame_of_frame)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the reuse path (`len uIn + 1 ≤ cap u`) -/
theorem mkR (impl : List Segment) (R : RtInv) (stkSN abSN : Nat) (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (hpre : Pre R b L c zp zc st up uc ip il vp vl s)
    (P : State) (hP : AtNat st up uc ip il ic vp vl vc zp zc s P)
    (S2 : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hA : AfterNat R b L st vl s P S2 stkSN abSN L1 b1)
    (hz : il + 1 ≤ uc) (Q : State → Prop)
    (k : ∀ S, AtU R b L zp zc st up uc ip il ic vp vl vc s (stW S2.mem st + 8 * stLen s.mem st) (stW S2.mem st)
      (stCap S2.mem st) L1 b1 L1 b1 up uc S → ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S2 Q := by
  have hE := env_of (S2 := S2.mem) hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow
    (fun a n v => by rw [hA.F2.accessible, hP.fr.accessible])
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hv2 := hl.v2; have hvil := hl.vil
  have hu40 := hpre.uo.1
  have p1 : S2.mem.readLE (s.sp.toNat + 56) 8 = uc := (rdS2 hpre hk1 hk2 hA _ _ (by omega) (by omega) (by omega)).trans hP.s7
  have p2 : S2.mem.readLE (s.sp.toNat - 136) 8 = il + 1 :=
    (rdS2 hpre hk1 hk2 hA _ _ (by omega) (by omega) (by omega)).trans hP.il1
  have p3 : S2.mem.readLE (s.sp.toNat + 40) 8 = up := (rdS2 hpre hk1 hk2 hA _ _ (by omega) (by omega) (by omega)).trans hP.s5
  obtain ⟨hal, hb', ha, hw⟩ := hpre.ce.2.1
  have hS2acc : ∀ a n v, S2.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hA.F2.accessible, hP.fr.accessible]
  have hwacc : S2.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hS2acc]; exact hw
  have hpc2 := hA.pc; have hsp2 := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hr0 := hA.r0; have hr1 := hA.r1; have hr2 := hA.r2
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
  -- `uIn` in `S2.mem`
  have hiS : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have hiw := hl.iw; have hsi := hpre.si
    unfold Apart at hsi
    rw [Held.readLE2 (hpre.io.2.2.2.1.sub h1 h2) hA.F2 hA.LF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega),
      hP.fr.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
  janus_run [p1, p2, p3] until [joinU]
  have hMF : MemFrame S2.mem ((((((S2.mem.writeLE (s.sp.toNat - 96) 8 (stW S2.mem st + 8 * stLen s.mem st)).writeLE
      (s.sp.toNat - 160) 8 vl).writeLE (s.sp.toNat - 152) 8 vl).writeLE (s.sp.toNat - 176) 8 uc).writeLE
      (s.sp.toNat - 192) 8 (il + 1)).writeLE (s.sp.toNat - 104) 8 up) (slotsW s) := by
    simp only [slotsW]; janus_frame
  refine k _ ⟨?qpc, rfl, ?q28, ?q29, ?q18, hr0, ?q1, ?q2, ?q3, ?q4, ?q5, ?qmem, ?qC, ?qL, ?qP, ?qua, LiveExt.refl R L1,
    Nat.sub_le _ _, ?qis⟩
  case qpc => janus_simp
  case q28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case q29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  case q18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
  case q1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hr1]
  case q2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hr2]
  case q3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q5 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case qmem =>
    refine mem_of_nat hE hk1 hk2 hP hA.F2 hA.LF2 rfl hA.len rfl (hMF.widen R.rt)
      (liveFrame_of_frame (rs := slotsW s) (ws := []) (lo := s.sp.toNat - 41264) (hi := s.sp.toNat + 112)
        (by simpa using hMF) hl.lsep (fun r hr => by
          simp only [slotsW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega))
      (by janus_simp; have := hl.t48; omega) (by janus_simp) (by janus_simp) ?_
    refine RtInv.inv_frame' hMF (fun r hr => ?_) hA.inv
    simp only [slotsW, List.mem_cons, List.not_mem_nil, or_false] at hr
    left
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hout.of_sub (by dsimp only; omega) (by dsimp only; omega)
  case qC => janus_simp
  case qL => janus_simp
  case qP => janus_simp; have := (hpre.uo.2.1 (by omega)).2.2.2; omega
  case qua =>
    exact uarr_reuse hE hz (fun a n w => by simp only [Memory.accessible_writeLE]; exact hS2acc a n w)
  case qis =>
    intro a n h1 h2
    have hiw := hl.iw
    rw [hMF.readLE a n (by simp only [slotsW, outside_cons, outside_nil, and_true]; omega)]
    exact hiS a n h1 h2

end FvModexp.Arm64.DivLarge
