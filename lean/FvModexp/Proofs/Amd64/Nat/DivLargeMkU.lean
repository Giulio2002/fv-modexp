import FvModexp.Proofs.Amd64.Nat.DivLargeMemN

set_option autoImplicit false

/-!
# `divLarge` (amd64): `u = u.make(len(uIn) + 1)` (natdiv.go:608), reuse path, from `stk.nat`'s return to `joinU`

`+0x125`: store `v` (`MOVQ AX/BX/CX` to `0xd0/0x90/0x98(SP')` = entry `RSP - 96, -160, -152`); `DX = BSR vIn[n-1]`;
`CMPQ SI = cap u, DI = len uIn + 1; JL` (signed) → allocation (`DivLargeMkA`); else `R8 = u.ptr`, `JMP joinU` (`+0x216`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open FvModexp (Held.readLE2 liveFrame_of_frame)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivLarge

set_option maxRecDepth 20000 in
/-- a frame slot at or above `RSP - 288` (outside `stk.nat`'s area and the stack's ranges): `S2` = `P` -/
theorem rdS2P {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (hpre : Pre R b L c zp zc st up uc ip il vp vl s) {P S2 : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hA : AfterNat R b L st vl s P S2 L1 b1) (a n : Nat) (h1 : (s.regs 4).toNat - 288 ≤ a)
    (h2 : a + n ≤ (s.regs 4).toNat + 112) : S2.mem.readLE a n = P.mem.readLE a n := by
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  obtain ⟨-, ⟨hb', ha, -⟩, -⟩ := hpre.ce
  have hb : 41272 ≤ (s.regs 4).toNat := hb'
  have hsw := hpre.sti.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hst : Apart a n st 24 := by unfold Apart; omega
  have hsa : 0 < stCap s.mem st → Apart a n (stW s.mem st) (8 * stCap s.mem st) := fun hc => by
    have := (hpre.sti.2.2.2 hc).1
    simp only [win, outside_cons, outside_nil, and_true] at this
    unfold Apart; omega
  rw [hA.F2.readLE a n ?_, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  rw [outside_append, outside_append]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩,
    outside_stkWs hpre hst hsa⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the reuse path (`len uIn + 1 ≤ cap u`) -/
theorem mkR (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (hpre : Pre R b L c zp zc st up uc ip il vp vl s)
    (hx : s.xmm 15 = 0#128) (hdf : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (P : State) (hP : AtNat st up uc il vp vl zp zc s P)
    (S2 : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hz : il + 1 ≤ uc) (Q : State → Prop)
    (k : ∀ S, AtU R b L zp zc st up uc ip il vp vl s (stW S2.mem st + 8 * stLen s.mem st) (stW S2.mem st)
      (stCap S2.mem st) L1 b1 L1 b1 up uc S → ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S2 Q := by
  have hS2acc : ∀ a n v, S2.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hA.F2.accessible, Janus.Arm64.Memory.accessible_writeLE, hP.fr.accessible]
  have hE := env_of hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow hS2acc hA.mem hx hdf hra
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hv2 := hl.v2; have hvil := hl.vil
  have hu40 := hpre.uo.1
  have p1 : S2.mem.readLE ((s.regs 4).toNat + 104) 8 = uc := (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.s7
  have p2 : S2.mem.readLE ((s.regs 4).toNat - 136) 8 = il + 1 := (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.il1
  have p3 : S2.mem.readLE ((s.regs 4).toNat + 88) 8 = up := (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.s5
  have p4 : S2.mem.readLE ((s.regs 4).toNat - 168) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8 :=
    (rdS2P hpre hA _ _ (by omega) (by omega)).trans hP.vtop
  have hpc2 := hA.pc; have hsp2 := hA.sp; have h5 := hA.r5; have h14 := hA.r14; have hfs := hA.fs
  have hx2 := hA.x15; have hdf2 := hA.df; have hr0 := hA.r0; have hr1 := hA.r1; have hr3 := hA.r3
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  obtain ⟨-, ⟨-, -, hw⟩, -⟩ := hpre.ce
  have hwacc : S2.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hS2acc]; exact hw
  have hvt : s.mem.readLE (vp + 8 * (vl - 1)) 8 ≠ 0 := by
    rcases hpre.vn with h | h
    · omega
    · exact h
  have hiS : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have hiw := hl.iw; have hsi := hpre.si
    unfold Apart at hsi
    rw [Held.readLE2 (hpre.io.2.2.2.1.sub h1 h2) hA.F2 hA.LF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hP.fr.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
  janus64_run [p1, p2, p3, p4] until [joinU]
  clear hbr
  have hMF : MemFrame S2.mem (((S2.mem.writeLE ((s.regs 4).toNat - 96) 8 (stW S2.mem st + 8 * stLen s.mem st)).writeLE
      ((s.regs 4).toNat - 160) 8 vl).writeLE ((s.regs 4).toNat - 152) 8 vl) (slotsW s) := by
    simp only [slotsW]; janus_frame
  refine k _ ⟨?qpc, ?qsp, ?q5, ?q14, ?qfs, ?qx, ?qdf, ?q0, ?q3, ?q1, ?q2, ?q6, ?q7, ?q8, ?qmem, ?qua,
    LiveExt.refl R L1, Nat.sub_le _ _, ?qis, ?qreg⟩
  case qpc => rfl
  case qsp => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp2]
  case q5 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h5]
  case q14 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14]
  case qfs => exact hfs
  case qx => exact hx2
  case qdf => rfl
  case q0 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hr0]
    try exact Nat.mod_eq_of_lt (by have := hl.t48; omega)
  case q3 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hr3]
  case q1 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hr1]
  case q2 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hvt]
  case q6 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q7 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q8 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case qreg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hA.reg
  case qmem =>
    refine mem_of_nat hE hP hA rfl hA.len rfl (hMF.widen R.rt)
      (liveFrame_of_frame (rs := slotsW s) (ws := []) (lo := (s.regs 4).toNat - 41272) (hi := (s.regs 4).toNat + 112)
        (by simpa using hMF) hl.lsep (fun r hr => by
          simp only [slotsW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega))
      (by janus_simp; have := hl.t48; omega) (by janus_simp) (by janus_simp) ?_
    refine RtInv.inv_frame' hMF (fun r hr => ?_) hA.inv
    simp only [slotsW, List.mem_cons, List.not_mem_nil, or_false] at hr
    left
    rcases hr with rfl | rfl | rfl | rfl <;> exact hout.of_sub (by dsimp only; omega) (by dsimp only; omega)
  case qua =>
    exact uarr_reuse hE hz (fun a n w => by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hS2acc a n w)
  case qis =>
    intro a n h1 h2
    have hiw := hl.iw
    rw [hMF.readLE a n (by simp only [slotsW, outside_cons, outside_nil, and_true]; omega)]
    exact hiS a n h1 h2

end FvModexp.Amd64.DivLarge
