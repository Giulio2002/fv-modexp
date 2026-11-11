import FvModexp.Proofs.Arm64.Nat.StackNatCall

/-!
# `(*stack).nat` (arm64): the `memclrNoHeapPointers` call of `slices.Grow` (after `growslice` returned the block
`(p, 8·gc)`) → the join `+0xd0` → `joinW`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

/-- the return site of the `memclr` call -/
abbrev pMR : Nat := segAddr Extracted.program fn + 0xac

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem g3 (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibStackNat.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hpre : Pre R b L 4208 24 st.toNat n.toNat s)
    (hk : stCap s.mem st.toNat < stLen s.mem st.toNat + rnd n.toNat) (p : Nat)
    (hpin : InRanges p (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) R.rt)
    (hp48 : p + 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) ≤ 2 ^ 48)
    (hal8 : p % 8 = 0)
    (hapL : ApartAll p (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) L)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : S.sp = s.sp - 112#64)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64) (h18 : S.regs 18 = s.regs 18)
    (h30 : S.regs 30 = BitVec.ofNat 64 pMR)
    (h0 : (S.regs 0).toNat = p + 8 * stCap s.mem st.toNat)
    (h1 : (S.regs 1).toNat = 8 * (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat))
    (hF : MemFrame s.mem S.mem (R.rt ++ winA s 4208 24))
    (hLF : LiveFrame s.mem S.mem L [])
    (hpacc : S.mem.accessible p (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)) true = true)
    (hinv : R.inv (b - 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))
      (L ++ [(p, p + 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))]) (s.regs 28).toNat
      (view R.rt (L ++ [(p, p + 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))]) S.mem))
    (slr : S.mem.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat)
    (sfp : S.mem.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (s48 : S.mem.readLE (s.sp.toNat - 48) 8 = growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))
    (s56 : S.mem.readLE (s.sp.toNat - 56) 8 = stLen s.mem st.toNat)
    (s24 : S.mem.readLE (s.sp.toNat - 24) 8 = stLen s.mem st.toNat + rnd n.toNat)
    (s16 : S.mem.readLE (s.sp.toNat - 16) 8 = p)
    (sst : S.mem.readLE (s.sp.toNat + 8) 8 = st.toNat) (sn : S.mem.readLE (s.sp.toNat + 16) 8 = n.toNat) :
    ReachesRet (LibStackNat.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L 4208 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre'
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  have hgcl := le_growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)
  have hgcb := growCap_lt (stLen s.mem st.toNat) n.toNat (stCap s.mem st.toNat) hk (by omega)
  have hgcc := growRound_le_cost (stLen s.mem st.toNat) n.toNat (stCap s.mem st.toNat) hk
  generalize growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) = gc at *
  have hpw := hpin.apart hout
  unfold Apart at hpw
  have hsp112 : S.sp.toNat = s.sp.toNat - 112 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hFw : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) := hF.mono fun a k h => by
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1, by omega, by omega⟩
  refine ReachesRet.call (hmc _ _) hpc (mcall_pre hpre hk S hFw (by omega) h28 (by rw [h30]; decide)
    (by rw [h30]; decide) rfl hgcl hpin hp48 hpacc hinv h0 h1) ?_
  intro S3 hpc3 ⟨junk, f3, v3, m3, ex3, ep3, hs3, hMF3, hLF3, hinv3, _⟩
  subst hs3
  simp only [calleeStack, hsp112, h0, h1] at hMF3 hLF3
  have hrd : ∀ a, (s.sp.toNat - 120 ≤ a ∧ a + 8 ≤ s.sp.toNat - 104) ∨ (s.sp.toNat - 88 ≤ a ∧ a + 8 ≤ s.sp.toNat + 24) →
      m3.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    refine hMF3.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
    have := (hpin.sub (a := p + 8 * stCap s.mem st.toNat)
      (n := 8 * (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat)) (by omega) (by omega)).apart
      (hout.of_sub (a := a) (n := 8) (by omega) (by omega))
    unfold Apart at this; omega
  have r48 := (hrd _ (by omega)).trans s48
  have r56 := (hrd _ (by omega)).trans s56
  have r24 := (hrd _ (by omega)).trans s24
  have r16 := (hrd _ (by omega)).trans s16
  have rst := (hrd _ (by omega)).trans sst
  have rn := (hrd _ (by omega)).trans sn
  have h30' : S.regs 30 = 1784348#64 := by rw [h30]; rfl
  have rlr := (hrd _ (by omega)).trans slr
  have rfp := (hrd _ (by omega)).trans sfp
  janus_run [r48, r56, r24, r16, rst, rn, hsp112, h30'] until [pJ]
  have hLs1 : LiveSep (L ++ [(p, p + 8 * gc)]) (win s 4208 24) := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [win, outside_cons, outside_nil, and_true]; omega
  have hext : LiveExt R L (L ++ [(p, p + 8 * gc)]) :=
    ⟨[(p, p + 8 * gc)], rfl, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]; exact ⟨hpin, hapL⟩,
      List.pairwise_singleton _ _⟩
  have hJ : J R b L st.toNat n.toNat s (L ++ [(p, p + 8 * gc)]) (b - 8 * gc) p gc m3 := by
    refine ⟨hpre, hl4, hl48, rlr, rfp, ?_, ?_, ?_, by omega, by rw [← h28]; exact hinv3, ?_, hgcl, hgcb, by omega,
      fun h => absurd h (by omega), fun _ => ⟨hpin, hapL⟩, hLs1, ?_⟩
    · refine hF.trans hMF3 fun a k ho => ⟨ho, ?_⟩
      simp only [wJ, winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hrt, h1, h2⟩ := ho
      refine ⟨⟨hrt, by omega, by omega⟩, ?_⟩
      have := (hpin.sub (a := p + 8 * stCap s.mem st.toNat)
        (n := 8 * (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat)) (by omega) (by omega)).apart hrt
      unfold Apart at this; omega
    · refine ⟨fun a k hin _ => ?_⟩
      rw [hLF3.readLE a k (hext.inRanges_old hin) ?_,
        hLF.readLE a k hin trivial]
      simp only [outside_cons, outside_nil, and_true]
      have := hapL.apart_of_inRanges hin; omega
    · exact hext
    · intro _
      exact ⟨hal8, Or.inl ⟨(p, p + 8 * gc), List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
        by simp only; omega⟩, by rw [← hF.accessible]; exact hpacc, hp48⟩
    · intro _; simp only [win, outside_cons, outside_nil, and_true]; omega
  refine joinW impl R hwb b L st n s _ _ p gc m3 hJ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | rfl | janus_simp

end FvModexp.Arm64.StackNat
