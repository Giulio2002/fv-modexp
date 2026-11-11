import FvModexp.Proofs.Arm64.Nat.StackNatG2
import FvModexp.Proofs.Common.DivmcBits

/-!
# `(*stack).nat` (arm64): entry → the join when the array is full (`cap < len + nr`): `slices.Grow` =
`growslice(w, len + nr, cap, len + nr - cap, Word)` + `memclrNoHeapPointers(p + 8·cap, 8·(len + nr - cap))`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem grow (impl : List Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract (LibStackNat.program.link impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibStackNat.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = st) (h1 : s.regs 1 = n)
    (hpre : Pre R b L 4208 24 st.toNat n.toNat s)
    (hk : stCap s.mem st.toNat < stLen s.mem st.toNat + rnd n.toNat) :
    ReachesRet (LibStackNat.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L 4208 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr', hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
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
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  obtain ⟨ht1, ht2, ht3⟩ := wT_facts hd
  have hwT : Apart wT 16 (s.sp.toNat - 4208) (4208 + 24) := apart_of_data hd 1 (by decide) (by decide) hw
  have hwTv : wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3 hwT
  unfold Apart at hwT
  simp only [stLen, stCap] at hti hk hlc hcb hln
  have hgro := hsv.2.2.2.1
  have hca : s.mem.readLE (st.toNat + 16) 8 + (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8)
      = s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat := by omega
  have hcb2 : s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat -
      s.mem.readLE (st.toNat + 16) 8) = s.mem.readLE (st.toNat + 16) 8 := by omega
  have hokg := hgro (s.mem.readLE st.toNat 8) (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) (s.mem.readLE (st.toNat + 16) 8)
    (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8) 2641088 (by omega)
  have hc0 : 0 < s.mem.readLE (st.toNat + 16) 8 → s.mem.readLE st.toNat 8 + 8 * s.mem.readLE (st.toNat + 16) 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) false = true := fun h => by
    obtain ⟨-, -, a3, a4⟩ := hnl h; exact ⟨a4, Memory.accessible_weaken _ a3⟩
  have e5 : BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8) + BitVec.ofNat 64 (rnd n.toNat) =
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e3 : BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) - BitVec.ofNat 64 (s.mem.readLE (st.toNat + 16) 8) =
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e1 : BitVec.ofNat 64 (s.mem.readLE (st.toNat + 16) 8) +
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat - s.mem.readLE (st.toNat + 16) 8) =
      BitVec.ofNat 64 (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e5] at hti
  janus_run [hr, h63, hacc16, hacc8, hti, e5, e3, e1, sub_mod64 (s.mem.readLE (st.toNat + 16) 8)
    (s.mem.readLE (st.toNat + 8) 8 + rnd n.toNat) (by omega) (by omega), hca, hcb2]
    until [cA "runtime.growslice"]
  have hsp112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hW64 : s.mem.readLE st.toNat 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  refine g2 impl R hgr hmc hwb b L st n s hl4 hl48 hpre (by simp only [stLen, stCap]; omega) _ ?gpc ?gsp ?g28 ?g29
    ?g18 ?g30 ?g0 ?g1 ?g2 ?g3 ?g4 ?gF ?slr ?sfp ?s40 ?s32 ?s56 ?s24 ?sst ?sn
  case gF => simp only [winA]; janus_frame
  case g0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stW]; omega
  case g1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stLen]; omega
  case g2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stCap]; omega
  case g3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, stLen, stCap]; omega
  case g4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; rfl
  all_goals janus_simp

end FvModexp.Arm64.StackNat
