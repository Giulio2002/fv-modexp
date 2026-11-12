import FvModexp.Proofs.Arm64.Nat.StackNatTail

/-!
# `(*stack).nat` (arm64): the join `+0xd0` → the header's `len`/`cap` stores, the write-barrier flag test and (flag on)
`gcWriteBarrier2` with its buffer stores `(new ptr, old ptr)` → `+0xec`, then `tail`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

/-- a store-only frame is a live frame -/
theorem lf_of_mf {m m' : Memory} {L ws : List (Nat × Nat)} (h : MemFrame m m' ws) : LiveFrame m m' L ws :=
  ⟨fun a n _ ho => h.readLE a n ho⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem joinW (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M : Memory) (h : J R b L st.toNat n.toNat s L1 b1 w1 c1 M)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pJ) (hsp : S.sp = s.sp - 112#64) (h0 : S.regs 0 = st)
    (h1 : S.regs 1 = n) (h2 : S.regs 2 = BitVec.ofNat 64 c1)
    (h5 : S.regs 5 = BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat)) (h6 : S.regs 6 = BitVec.ofNat 64 w1)
    (h7 : S.regs 7 = BitVec.ofNat 64 (stLen s.mem st.toNat)) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 120#64) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibStackNat.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostL R b L 4208 24 st.toNat n.toNat s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, hwbf, hwbA, hfa⟩ := hpre
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  have hc1len := h.c1len
  have hc1b := h.c1b
  have hw64 := h.w64
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hsp112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hstaccM : M.accessible st.toNat 24 true = true := by rw [h.mf.accessible]; exact hstacc
  have hacc16 : M.accessible (st.toNat + 8) 16 true = true := Memory.accessible_mono _ hstaccM (by omega) (by omega)
  have hacc8 : M.accessible st.toNat 8 false = true := Memory.accessible_weaken _ (Memory.accessible_mono _ hstaccM (by omega) (by omega))
  have hwbM : M.accessible wbA 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hwbv : wbA = 7616064 := rfl
  rw [hwbv] at hwbA
  unfold Apart at hwbA
  have hlr4 := h.lr4
  have hlr48 := h.lr48
  have hsth1 := h.ext.held hsth
  have hinvW : ∀ v1 v2, R.inv b1 L1 (s.regs 28).toNat
      (view R.rt L1 ((M.writeLE (st.toNat + 8) 8 v1).writeLE (st.toNat + 16) 8 v2)) := fun v1 v2 =>
    RtInv.inv_frame' (ws := [(st.toNat, st.toNat + 24)]) (by janus_frame)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [show st.toNat + 24 - st.toNat = 24 by omega]; exact hsth1.symm) h.inv
  janus_run [hm, hsp112, hacc16, hacc8, hwbM] until [cA "runtime.gcWriteBarrier2", pS]
  · -- the barrier is off
    refine tail impl R b L st n s L1 b1 w1 c1 M _ h ?_ ?_ (hinvW _ _) ?_ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · janus_frame
    · exact lf_of_mf (by janus_frame)
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    all_goals janus_simp
  · -- the barrier is on
    have hwb2 := hsv.2.2.2.2.2.1 [2]
    have hLW : LiveSep L1 [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8)] := fun r hr => by
      have := h.lsep r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    have hWR : LiveSep [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8)] R.rt := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hout.of_sub (by omega) (by simp; omega)
    have hwacc : M.accessible (s.sp.toNat - 4208) (4096 + 8) true = true := by
      rw [h.mf.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    refine ReachesRet.call (hwb L1 b1) ?_ ⟨⟨?_, ?_, ?_, ?_, by omega, ?_, ?_⟩, hwb2, ?_, ?_, ?_⟩ ?_
    · rfl
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · dsimp only; rw [hsp112]; omega
    · dsimp only; rw [hsp112]; omega
    · dsimp only; rw [hsp112]; omega
    · dsimp only; rw [hsp112, Memory.accessible_writeLE, Memory.accessible_writeLE]
      rw [show s.sp.toNat - 112 - 4096 = s.sp.toNat - 4208 by omega]; exact hwacc
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]; exact hinvW _ _
    · dsimp only; rw [hsp112]; exact hLW
    · dsimp only; rw [hsp112]; exact hWR
    intro S2 hpc2 ⟨buf, junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
    subst hs2
    dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
    rw [hsp112] at hfr2 hapW
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28] at hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hacc16b : m'.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hacc16b (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hstb : st.toNat + 24 ≤ buf.toNat ∨ buf.toNat + 16 ≤ st.toNat := by
      rcases hsth1 with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hkeep : ∀ a k, st.toNat ≤ a → a + k ≤ st.toNat + 24 →
        m'.readLE a k = ((M.writeLE (st.toNat + 8) 8 (stLen s.mem st.toNat)).writeLE (st.toNat + 16) 8 c1).readLE a k := by
      intro a k h1 h2
      rcases hsth1 with hL | hO
      · exact hlf2.readLE a k (hL.sub h1 h2) trivial
      · refine hfr2.readLE a k ?_
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hO.of_sub h1 h2, by omega⟩
    have hF1 : MemFrame M ((M.writeLE (st.toNat + 8) 8 (stLen s.mem st.toNat)).writeLE (st.toNat + 16) 8 c1)
        [(st.toNat, st.toNat + 24)] := by janus_frame
    janus_run [hb8a, hb8b, hbuf64] until [pS]
    have hbs : MemFrame m' ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8))
        [(buf.toNat, buf.toNat + 16)] := by janus_frame
    refine tail impl R b L st n s L1 b1 w1 c1 M _ h ?_ ?_ ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · refine MemFrame.trans (rs := R.rt ++ [(st.toNat, st.toNat + 24), (s.sp.toNat - 4208, s.sp.toNat - 120)])
        (MemFrame.trans (rs'' := R.rt ++ [(st.toNat, st.toNat + 24), (s.sp.toNat - 4208, s.sp.toNat - 120)])
          hF1 hfr2 (fun a k ho => ?_)) hbs (fun a k ho => ?_)
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨ho.2.1, ho.1, by omega⟩
      · refine ⟨ho, ?_⟩
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        have := hbufR.apart ho.1; unfold Apart at this; omega
    · refine ⟨fun a k hin hout => ?_⟩
      rw [hbs.readLE a k ?_, hlf2.readLE a k hin trivial, hF1.readLE a k hout]
      simp only [outside_cons, outside_nil, and_true]
      have := hapL.apart_of_inRanges hin; omega
    · have hv1 : view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8)) =
          ((view R.rt L1 m').writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8) := by
        rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
          view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
      rw [hv1]
      exact hinvS _ (by janus_frame)
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hkeep _ _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hkeep _ _ (by omega) (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    all_goals janus_simp

end FvModexp.Arm64.StackNat
