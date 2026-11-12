import FvModexp.Proofs.Amd64.Nat.StackNatG2
import FvModexp.Proofs.Common.DivmcBits

/-!
# `(*stack).nat` (amd64): entry → the `growslice` call when the array is full (`cap < len + nr`): `slices.Grow` =
`growslice(w, len + nr, cap, len + nr - cap, Word)` + `memclrNoHeapPointers(p + 8·cap, 8·(len + nr - cap))`
(the `JAE` that skips `growslice` when `cap + num` wraps is refuted: `num = len + nr - cap` is small)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNat

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem grow (impl : List Amd64.Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (LibStackNat.program.link impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibStackNat.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = st) (h3 : s.regs 3 = n)
    (hpre : Pre R b L 4192 24 st.toNat n.toNat s)
    (hk : stCap s.mem st.toNat < stLen s.mem st.toNat + rnd n.toNat) :
    ReachesRet (LibStackNat.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostL R b L 4192 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr', hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
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
  have e9 : BitVec.ofNat 64 (rnd n.toNat) - (BitVec.ofNat 64 (s.mem.readLE (st.toNat + 16) 8) -
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8)) =
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e10 : BitVec.ofNat 64 (s.mem.readLE (st.toNat + 16) 8) +
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8) =
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e10' : BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8) +
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 16) 8) =
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hti9 : (BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8)).toInt =
      ((s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8 : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have hlt : BitVec.ofNat 64 (s.mem.readLE (st.toNat + 16) 8) ≤
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) := by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  janus64_run [hr, hacc24, hti, e9, e10, e10', hti9, hlt, BitVec.msb_eq_decide] until [cA "runtime.growslice"]
  have hsp96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  refine g2 impl R hgr hmc hwb b L st n s hra hx15 hdf hpre hk _ ?gpc ?gsp ?g14 ?g5 ?gx ?gfs ?gdf ?sret ?g0 ?g3 ?g1 ?g7
    ?g6 ?gF ?sra ?sbp ?s30 ?s20 ?s18 ?sst ?sn
  case gF => simp only [win]; janus_frame
  case gpc => rfl
  case gx => rfl
  case gfs => rfl
  case gdf => first | exact hdf | (simp only [hdf]) | janus64_simp
  case g0 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stW]
    have := Janus.Arm64.Memory.readLE_lt s.mem st.toNat 8; omega
  case g1 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stCap]; omega
  case g3 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, stLen]
  case g7 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stLen, stCap]; omega
  case g6 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; rfl
  case g14 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g5 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case gsp => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case sret => rw [Janus.Arm64.Memory.readLE_writeLE_self]
  all_goals first
    | (janus64_simp; done)
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
        stLen, stCap]; omega)
    | skip

end FvModexp.Amd64.StackNat
