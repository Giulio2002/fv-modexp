import FvModexp.Proofs.Amd64.Nat.StackNatXWb

set_option autoImplicit false

/-!
# `(*stack).nat` (amd64): entry → the join when the array has room (`len + nr ≤ cap`: `slices.Grow` is a no-op)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNatX

open FvModexp.Amd64.StackNat (fn names wbA rnd)

theorem rnd_bv (n : BitVec 64) (h : n.toNat ≤ 2 ^ 16) :
    (n + 3#64) &&& BitVec.ofNat 64 18446744073709551612 = BitVec.ofNat 64 (rnd n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [stackRound_toNat n (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [rnd]; omega)]

/-- the signed difference `nr - (cap - len)` of `slices.Grow`'s test (amd64 form) -/
theorem toInt_sub3' (a r c : Nat) (ha : a < 2 ^ 60) (hr : r < 2 ^ 60) (hc : c < 2 ^ 60) (hac : a ≤ c) :
    (BitVec.ofNat 64 r - (BitVec.ofNat 64 c - BitVec.ofNat 64 a)).toInt = (a : Int) + r - c := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem noGrow (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = st) (h3 : s.regs 3 = n)
    (hpre : PreX R b L 4192 24 st.toNat n.toNat s)
    (hk : stLen s.mem st.toNat + rnd n.toNat ≤ stCap s.mem st.toNat) :
    ReachesRet (LibStackNat.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostXL R b L 4192 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, hwbf, hwbA, hfa⟩ := hpre'
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  unfold Apart at hga
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hacc24 : s.mem.accessible st.toNat 24 false = true := Janus.Arm64.Memory.accessible_weaken _ hstacc
  have hr := rnd_bv n hn16
  have hti := toInt_sub3' (stLen s.mem st.toNat) (rnd n.toNat) (stCap s.mem st.toNat) (by omega)
    (by simp only [rnd]; omega) (by omega) hlc
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  simp only [stLen, stCap] at hti hk hlc hcb hln
  janus64_run [hr, hacc24, hti, BitVec.msb_eq_decide] until [pJ]
  have hF : MemFrame s.mem (s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat) (win s 4192 24) := by
    simp only [win]; janus_frame
  have hcl := harr
  refine joinW impl R hwb b L st n s L (b - 0) (stW s.mem st.toNat) (stCap s.mem st.toNat) _ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ rfl
  · refine ⟨hpre, hra, ?_, ?_, hF.mono fun a k h => by rw [outside_append] at h; exact h.2, LiveFrame.of_win hF hLs,
      LiveExt.refl R L,
      ⟨fun _ => by omega, fun h => absurd h (by simp only [stLen, stCap] at hk ⊢; omega)⟩, ?_, hnl, hk, hcb, by simp only [stW]; exact Janus.Arm64.Memory.readLE_lt _ _ _,
      fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp only [stLen, stCap]; omega), hLs, fun h => (hcl h).1, hdf,
      fun h => absurd h (by simp only [stLen, stCap]; omega)⟩
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    · rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (BitVec.isLt _)]
    · exact RtInv.inv_frame hF (fun r hr => by
        simp only [win, List.mem_singleton] at hr; subst hr; simp only
        rw [show (s.regs 4).toNat + 24 - ((s.regs 4).toNat - 4192) = 4192 + 24 by omega]; exact hout)
        (by simpa using hinv0)
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, stW, stLen, stCap, h0, h3, hx15, hdf]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.StackNatX
