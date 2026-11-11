import FvModexp.Proofs.Arm64.Nat.StackNatG3
import FvModexp.Proofs.Common.DivmcLsl

/-!
# `(*stack).nat` (arm64): the `growslice` call of `slices.Grow` → the `memclrNoHeapPointers` call (`g3`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem g2 (impl : List Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract (LibStackNat.program.link impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibStackNat.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hpre : Pre R b L 4208 24 st.toNat n.toNat s)
    (hk : stCap s.mem st.toNat < stLen s.mem st.toNat + rnd n.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 (cA "runtime.growslice")) (hsp : S.sp = s.sp - 112#64)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64) (h18 : S.regs 18 = s.regs 18)
    (h30 : S.regs 30 = 1784300#64)
    (h0 : (S.regs 0).toNat = stW s.mem st.toNat) (h1 : (S.regs 1).toNat = stLen s.mem st.toNat + rnd n.toNat)
    (h2 : (S.regs 2).toNat = stCap s.mem st.toNat)
    (h3 : (S.regs 3).toNat = stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat) (h4 : (S.regs 4).toNat = wT)
    (hF : MemFrame s.mem S.mem (winA s 4208 24))
    (slr : S.mem.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat)
    (sfp : S.mem.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (s40 : S.mem.readLE (s.sp.toNat - 40) 8 = stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat)
    (s32 : S.mem.readLE (s.sp.toNat - 32) 8 = stCap s.mem st.toNat)
    (s56 : S.mem.readLE (s.sp.toNat - 56) 8 = stLen s.mem st.toNat)
    (s24 : S.mem.readLE (s.sp.toNat - 24) 8 = stLen s.mem st.toNat + rnd n.toNat)
    (sst : S.mem.readLE (s.sp.toNat + 8) 8 = st.toNat) (sn : S.mem.readLE (s.sp.toNat + 16) 8 = n.toNat) :
    ReachesRet (LibStackNat.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L 4208 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr', hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre'
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  have hsp112 : S.sp.toNat = s.sp.toNat - 112 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hFw : MemFrame s.mem S.mem [(s.sp.toNat - 4208, s.sp.toNat + 24)] := hF.mono fun a k h => by
    simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  refine ReachesRet.call (hgr L b) hpc (gcall_pre hpre hk S hFw (by omega) h28 (by rw [h30]; decide)
    (by rw [h30]; decide) h0 h1 h2 h3 h4) ?_
  intro S1 hpc1 ⟨ptr, junk, f1, v1, m1, ex1, ep1, hs1, hMF, hLF, ⟨hobj, hapL⟩, hapS, hinv1⟩
  subst hs1
  have hround : growsliceRound S = 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) := by
    simp only [growsliceRound, h1, h2]
  simp only [growsliceObj, Fresh, h1, h2, h3, hround] at hobj
  rw [hround] at hapL hinv1
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, -, -⟩ := hobj
  have hgcl := le_growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)
  have hgcb := growCap_lt (stLen s.mem st.toNat) n.toNat (stCap s.mem st.toNat) hk (by omega)
  have hpw := hpin.apart hout
  unfold Apart at hpw
  simp only [calleeStack, hsp112] at hMF
  have hrd : ∀ a, (s.sp.toNat - 120 ≤ a ∧ a + 8 ≤ s.sp.toNat - 104) ∨ (s.sp.toNat - 64 ≤ a ∧ a + 8 ≤ s.sp.toNat + 24) →
      m1.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have r40 := (hrd _ (by omega)).trans s40
  have r32 := (hrd _ (by omega)).trans s32
  have r24 := (hrd _ (by omega)).trans s24
  have r56 := (hrd _ (by omega)).trans s56
  have rst := (hrd _ (by omega)).trans sst
  have rn := (hrd _ (by omega)).trans sn
  have rlr := (hrd _ (by omega)).trans slr
  have rfp := (hrd _ (by omega)).trans sfp
  have h30' : S.regs 30 = 1784300#64 := h30
  have hgc64 : growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) < 2 ^ 64 := by omega
  have hp64 : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hS1 : S.regs 1 = BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have esub : BitVec.ofNat 64 (stCap s.mem st.toNat) + BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat) -
      BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat) = BitVec.ofNat 64 (stCap s.mem st.toNat) :=
    BitVec.add_sub_cancel _ _
  have hl3 := lsl3_ofNat (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat) (by omega)
  janus_run [r40, r32, r24, r56, rst, rn, hsp112, h30', hS1, esub, hl3, h2] until [cA "runtime.memclrNoHeapPointers"]
  have hLw : LiveSep L (winA s 4208 24) := liveSep_winA hLs
  have hst2 : MemFrame m1 ((m1.writeLE (s.sp.toNat - 48) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE (s.sp.toNat - 16) 8 ptr.toNat)
      [(s.sp.toNat - 48, s.sp.toNat - 40), (s.sp.toNat - 16, s.sp.toNat - 8)] := by janus_frame
  have hwr : LiveSep [(s.sp.toNat - 48, s.sp.toNat - 40), (s.sp.toNat - 16, s.sp.toNat - 8)] R.rt := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  have hF1 : MemFrame s.mem m1 (R.rt ++ winA s 4208 24) := by
    refine MemFrame.trans hF hMF fun a k ho => ?_
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1, h2⟩ := ho
    exact ⟨⟨h1, h2⟩, hrt, by omega, by omega⟩
  have hF2 := hF1.trans hst2 fun a k ho => by
    refine ⟨ho, ?_⟩
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hLF2 : LiveFrame s.mem ((m1.writeLE (s.sp.toNat - 48) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE (s.sp.toNat - 16) 8 ptr.toNat)
      L [] := by
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLw r hr
    simp only [winA, outside_cons, outside_nil, and_true] at this
    rw [hst2.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF.readLE a k ⟨r, hr, h1, h2⟩ trivial, hF.readLE a k (by simp only [winA, outside_cons, outside_nil, and_true]; omega)]
  have hpacc2 : ((m1.writeLE (s.sp.toNat - 48) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE (s.sp.toNat - 16) 8 ptr.toNat).accessible
      ptr.toNat (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) true = true := by
    simp only [Memory.accessible_writeLE]; exact hpacc
  have hinv2 := RtInv.inv_frame hst2 hwr hinv1
  rw [h28] at hinv2
  have q48 : ((m1.writeLE (s.sp.toNat - 48) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE (s.sp.toNat - 16) 8 ptr.toNat).readLE
      (s.sp.toNat - 48) 8 = growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) := by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have q16 : ((m1.writeLE (s.sp.toNat - 48) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE (s.sp.toNat - 16) 8 ptr.toNat).readLE
      (s.sp.toNat - 16) 8 = ptr.toNat := by
    rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have qk : ∀ a, (a + 8 ≤ s.sp.toNat - 48 ∨ s.sp.toNat - 40 ≤ a) → (a + 8 ≤ s.sp.toNat - 16 ∨ s.sp.toNat - 8 ≤ a) →
      ((m1.writeLE (s.sp.toNat - 48) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE (s.sp.toNat - 16) 8 ptr.toNat).readLE
      a 8 = m1.readLE a 8 := fun a h1 h2 => by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  refine g3 impl R hmc hwb b L st n s hl4 hl48 hpre hk ptr.toNat hpin hp48 (hal8 (Or.inr (by omega))) hapL _ rfl rfl
    ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact h28
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact h29
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, callRegs_apply]; exact h18
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
  · exact hF2
  · exact hLF2
  · exact hpacc2
  · exact hinv2
  · exact (qk _ (by omega) (by omega)).trans rlr
  · exact (qk _ (by omega) (by omega)).trans rfp
  · exact q48
  · exact (qk _ (by omega) (by omega)).trans r56
  · exact (qk _ (by omega) (by omega)).trans r24
  · exact q16
  · exact (qk _ (by omega) (by omega)).trans rst
  · exact (qk _ (by omega) (by omega)).trans rn

end FvModexp.Arm64.StackNat
