import FvModexp.Proofs.Amd64.NatQ.DivLargeMkU
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeMkA.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `u = u.make(len(uIn) + 1)` (natdiv.go:608), allocation path (`cap u < len uIn + 1`)

`+0x125`: store `v` (`SP' + 0xd0/0x90/0x98` = entry `RSP - 96, -160, -152`); `DX = BSR vIn[n-1]`; `CMPQ SI = cap u,
DI = len uIn + 1; JL` taken → `+0x176`: spill `DX` (`RSP - 120`); `TESTQ SI = len uIn` (`≠ 0`: `2 ≤ len v ≤ len uIn`, so
the `makeslice(Word, 1, 1)` branch at `+0x19a` is dead); `CX = len uIn + 5` spilled at `RSP - 184`;
`makeslice(Word, len uIn + 1, len uIn + 5)` (`+0x1e1`); reload `CX, DX, BX, SI, DI, AX`, `R8 = ptr`, `JMP joinU`.
Port of `Arm64/Nat/DivLargeMkA.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open FvModexp (Held.readLE2 liveFrame_of_frame)
open FvModexp.Amd64.DivBasic (LiveFrame.trans')

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

/-- `big.Word`'s type descriptor (read-only data) -/
abbrev wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
/-- the allocation path (`cap u < len uIn + 1`): `makeslice(Word, len uIn + 1, len uIn + 5)` -/
theorem mkA (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDivL.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (hpre : Pre R b H L c zp zc st up uc ip il vp vl s)
    (hx : s.xmm 15 = 0#128) (hdf : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (P : State) (hP : AtNat st up uc il vp vl zp zc s P)
    (S2 : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hA : AfterNat R b H L st vl s P S2 L1 b1)
    (hz : uc < il + 1) (hb1 : makeCost (il + 1) ≤ b1) (Q : State → Prop)
    (k : ∀ S Lk bk P' C', AtU R b L zp zc st up uc ip il vp vl s (stW S2.mem st + 8 * stLen s.mem st)
      (stW S2.mem st) (stCap S2.mem st) L1 b1 Lk bk P' C' S → ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S2 Q := by
  have hS2acc : ∀ a n v, S2.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hA.F2.accessible, Janus.Arm64.Memory.accessible_writeLE, hP.fr.accessible]
  have hE := env_of hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow hS2acc hA.mem hx hdf hra
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hv2 := hl.v2; have hvil := hl.vil
  have hu40 := hpre.uo.1
  have p2 : S2.mem.readLE ((s.regs 4).toNat - 136) 8 = il + 1 := (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.il1
  have p4 : S2.mem.readLE ((s.regs 4).toNat - 168) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8 :=
    (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.vtop
  have p1 : S2.mem.readLE ((s.regs 4).toNat + 104) 8 = uc := (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.s7
  have p5 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = il :=
    (rdS2P hpre hA _ _ (by omega) (by omega)).trans
      ((hP.fr.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)).trans hpre.ilS)
  have hvt : s.mem.readLE (vp + 8 * (vl - 1)) 8 ≠ 0 := by
    rcases hpre.vn with h | h
    · omega
    · exact h
  have hpc2 := hA.pc; have hsp2 := hA.sp; have h5 := hA.r5; have h14 := hA.r14; have hfs := hA.fs
  have hx2 := hA.x15; have hdf2 := hA.df; have hr0 := hA.r0; have hr1 := hA.r1; have hr3 := hA.r3
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  have hd : Extracted.program.DataLoaded s.mem := hpre.ce.2.2.2.1
  have hro : RoOut R := hpre.ce.2.2.2.2.2.2.2.2.1
  have hga := hpre.ce.2.2.2.2.2.1
  have hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt := hpre.ce.2.2.2.2.2.2.1
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hpre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg hal
  have hwacc : S2.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hS2acc]; exact hw
  have hsv := hpre.sv
  have hiS : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have hiw := hl.iw; have hsi := hpre.si
    unfold Apart at hsi
    rw [Held.readLE2 (hpre.io.2.2.2.1.sub h1 h2) hA.F2 hA.LF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hP.fr.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
  -- a read of `s.mem` outside the frame writes, the pushed return address, `stk.nat`'s window and the stack ranges
  have hS2rd : ∀ a n, Outside a n R.rt ∨ True → Outside a n (R.rt ++ [((s.regs 4).toNat - 312 - 4192,
      (s.regs 4).toNat - 312 + 24)] ++ stkWs s.mem st) → (a + n ≤ (s.regs 4).toNat - 312 ∨ (s.regs 4).toNat - 304 ≤ a) →
      Outside a n (proWs s) → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n _ h1 h2 h3
    rw [hA.F2.readLE a n h1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hP.fr.readLE a n h3]
  have hk1' : il + 1 ≠ 1 := by omega
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 41272) (41272 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, il + 1, il + 5] := hsv.1 _ _ _ (by omega)
  have hmcost : makeCost (il + 1) = allocCost (8 * (il + 1 + 4)) := by unfold makeCost makeCap; rw [if_neg hk1']
  have hbl := blockSize_le_allocCost (8 * (il + 1 + 4)) true
  have hbs : blockSize (8 * (il + 1 + 4)) true ≤ b1 := by omega
  have hinv2 := hA.inv
  unfold Apart at hwt hga htw
  have hWw : Outside wordT 16 (stkWs s.mem st) := by
    have hstacc := hpre.sti.1.2.2.1
    refine outside_stkWs hpre (apart_of_data hd 1 (by decide) (by decide) hstacc) fun hc => ?_
    exact apart_of_data hd 1 (by decide) (by decide) (hpre.sti.1.2.2.2.2.1 hc).2.2.1
  have hWr : ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have h3 := hWw.of_sub h1 (show a + n ≤ wordT + 16 by omega)
    simp only [stkWs, outside_cons, outside_nil, and_true] at h3
    refine hS2rd a n (Or.inr trivial) ?_ (by omega) (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hty.of_sub h1 (by omega), by omega⟩, h3⟩
  have hgW : Outside ((s.regs 14).toNat + 16) 8 (stkWs s.mem st) := by
    refine outside_stkWs hpre (hpre.sti.2.2.1.symm) fun hc => ?_
    exact (hpre.sti.2.2.2 hc).2.symm
  have hgS : S2.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    simp only [stkWs, outside_cons, outside_nil, and_true] at hgW
    refine hS2rd _ _ (Or.inr trivial) ?_ (by omega) (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hgr, by omega⟩, hgW⟩
  have htS : S2.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [← htg]
    have hTW : Outside (s.fsBase.toNat - 8) 8 (stkWs s.mem st) := by
      have hstt := hpre.stt; unfold Apart at hstt
      have hft := hpre.stft; unfold Apart at hft
      simp only [stkWs, outside_cons, outside_nil, and_true]; omega
    simp only [stkWs, outside_cons, outside_nil, and_true] at hTW
    refine hS2rd _ _ (Or.inr trivial) ?_ (by omega) (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨htrt, by omega⟩, hTW⟩
  have hgacc : S2.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hS2acc]; exact hg2
  obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : S2.mem.readLE 7233184 8 = 8 := (hWr _ _ (by omega) (by omega)).trans hws
  have hT2 : S2.mem.readLE 7233192 8 = 0 := (hWr _ _ (by omega) (by omega)).trans hwp
  have hTa : S2.mem.accessible 7233184 16 false = true := (hS2acc _ _ _).trans hwa
  have hLs1 := hl.lsep
  have hc1 := hE.c1len
  have hil0 : (BitVec.ofNat 64 il = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hw1h : Held R L1 (stW S2.mem st) (8 * stCap S2.mem st) := (hA.ok.2.2.2.2.1 (by
    simp only [StackNat.rnd] at hc1; omega)).2.1
  janus64_run [p1, p2, p4, p5, hil0, hT1, hT2, hTa, hgS, htS] until [joinU] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ _ _
  clear hbr
  have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
  have hptr : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hM : MemFrame S2.mem m (R.rt ++ slotsW s) := MemFrame.trans (rs := slotsW s)
    (by simp only [slotsW]; janus_frame) hMF (fun a n h => by
      simp only [slotsW, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨hrt, h1, h2, h3, h4⟩ := h
      exact ⟨⟨h1, h2, h3, h4⟩, hrt, by omega, by omega⟩)
  have hML : LiveFrame S2.mem m L1 [] :=
    LiveFrame.trans' (liveFrame_of_frame (rs := slotsW s) (ws := []) (lo := (s.regs 4).toNat - 41272)
      (hi := (s.regs 4).toNat + 112) (by simp only [slotsW, List.append_nil]; janus_frame) hl.lsep (fun r hr => by
        simp only [slotsW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega)) hLF
  have hblk : blockSize (8 * (il + 5)) true ≤ makeCost (il + 1) := by rw [hmcost]; exact hbl
  refine k _ (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (il + 5)) true)]) (b1 - blockSize (8 * (il + 5)) true)
    ptr.toNat (il + 1 + 4) ⟨?qpc, ?qsp, ?q5, ?q14, ?qfs, ?qx, ?qdf, ?q0, ?q3, ?q1, ?q2, ?q6, ?q7, ?q8, ?qmem, ?qua,
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, ?qis, ?qreg⟩
  case qreg => rw [hrg1]; exact hA.reg
  case qpc => rfl
  case qsp => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; bv_omega
  case q5 => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, h5]
  case q14 => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, or_true, h14]
  case qfs => exact hfs
  case qx => simp only [↓reduceIte]
  case qdf => rfl
  case q0 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by have := hl.t48; omega)]
  case q3 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q1 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q2 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hvt]
  case q6 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q7 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q8 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case qmem =>
    refine mem_of_nat hE hP hA rfl hA.len rfl hM hML ?_ ?_ ?_ hinv'
    · rw [hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
      janus_simp; have := hl.t48; omega
    · rw [hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
      janus_simp
    · rw [hMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)]
      janus_simp
  case qua =>
    refine uarr_alloc hE hz hAp hIn hle ?_ h8' (by omega) hw1h
    rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc
  case qis =>
    intro a n h1 h2
    have hiw := hl.iw
    rcases (hpre.io.2.2.2.1.sub h1 h2) with hi | ho
    · rw [hML.readLE a n (hE.ext.inRanges_old hi) (by simp)]; exact hiS a n h1 h2
    · rw [hM.readLE a n (by
        rw [outside_append]; exact ⟨ho, by simp only [slotsW, outside_cons, outside_nil, and_true]; omega⟩)]
      exact hiS a n h1 h2

end FvModexp.Amd64.Q.DivLarge
