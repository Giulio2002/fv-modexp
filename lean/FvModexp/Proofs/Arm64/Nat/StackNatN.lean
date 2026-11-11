import FvModexp.Proofs.Arm64.Nat.StackNatWb

/-!
# `(*stack).nat` (arm64): entry → the join when the array has room (`len + nr ≤ cap`: `slices.Grow` is a no-op)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

theorem rnd_bv (n : BitVec 64) (h : n.toNat ≤ 2 ^ 16) :
    (n + 3#64) &&& BitVec.ofNat 64 18446744073709551612 = BitVec.ofNat 64 (rnd n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [stackRound_toNat n (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [rnd]; omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noGrow (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = st) (h1 : s.regs 1 = n)
    (hpre : Pre R b L 4208 24 st.toNat n.toNat s)
    (hk : stLen s.mem st.toNat + rnd n.toNat ≤ stCap s.mem st.toNat) :
    ReachesRet (LibStackNat.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L 4208 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, hwbf, hwbA, hfa⟩ := hpre'
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  unfold Apart at hga
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hacc16 : s.mem.accessible st.toNat 16 false = true :=
    Memory.accessible_weaken _ (Memory.accessible_mono _ hstacc (by omega) (by omega))
  have hacc8 : s.mem.accessible (st.toNat + 16) 8 false = true :=
    Memory.accessible_weaken _ (Memory.accessible_mono _ hstacc (by omega) (by omega))
  have hr := rnd_bv n hn16
  have h63 : (BitVec.ofNat 64 (rnd n.toNat)).getLsbD 63 = false :=
    getLsbD63_false _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [rnd]; omega)]; simp only [rnd]; omega)
  have hti := toInt_sub3 (stLen s.mem st.toNat) (rnd n.toNat) (stCap s.mem st.toNat) (by omega)
    (by simp only [rnd]; omega) (by omega)
  simp only [stLen, stCap] at hti hk hlc hcb hln
  janus_run [hr, h63, hacc16, hacc8, hti] until [pJ]
  have hlen := hlc
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  refine joinW impl R hwb b L st n s L (b - 0) (stW s.mem st.toNat) (stCap s.mem st.toNat) _ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ rfl
  · have hF : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 112) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 120) 8
        (s.regs 29).toNat) (winA s 4208 24) := by simp only [winA]; janus_frame
    have hcl := hpre.2.2.2.2.1
    refine ⟨hpre, hl4, hl48, ?_, ?_, hF.mono fun a k h => by rw [outside_append] at h; exact h.2, LiveFrame.of_win hF
      (liveSep_winA hLs), LiveExt.refl R L, by omega, ?_, hnl, hk, hcb, by simp only [stW]; exact Memory.readLE_lt _ _ _,
      fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp only [stLen, stCap]; omega), hLs, fun h => (hcl h).1⟩
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    · exact inv_frame_winA hF hout (by omega) (by omega) (by simpa using hinv0)
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, stW, stLen, stCap, h0, h1]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.StackNat
