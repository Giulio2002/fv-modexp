import FvModexp.Proofs.Arm64.Int.IntASPost

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tailA (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State)
    (nb V cost p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (h : AtRet false R b L z x y s nb V cost p' l' c' b1 L1 S) (hpc : S.pc = BitVec.ofNat 64 (0x1b0910 + 0x58))
    (hnb : nb = hNeg s.mem x) :
    ReachesRet (LibIntAS.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post false R b L z x y s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, hsv, -, -, -, hza, hz48, hzo, hzH, hzg,
    hzwb, -, -, -, -, -, -, hwbf, -, -⟩ := hpre
  have hsp := h.sp; have h28 := h.r28; have h29 := h.r29; have h18 := h.r18
  have h0 := h.r0; have h1 := h.r1; have h2 := h.r2
  have hzs := h.zs; have hng := h.ng; have hfp := h.fp; have hlr := h.lr
  have hlr4 := h.lr4; have hlr48 := h.lr48
  have hc40 := h.c40; have hlc := h.lc; have hp64 := h.p64
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  unfold Apart at hzg hzwb
  have hwbv : wbA = 7616064 := rfl
  rw [hwbv] at hzwb
  have hsp96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hzaS : S.mem.accessible z 32 true = true := by rw [h.mf.accessible]; exact hza
  have hwbS : S.mem.accessible wbA 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hwS : S.mem.accessible (s.sp.toNat - 4560) (4560 + 32) true = true := by rw [h.mf.accessible]; exact hw
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  janus_run [hsp, hsp96, hzs, hng, hfp, hlr, hzaS, hwbS] until [cA "runtime.gcWriteBarrier2"]
  · exact post_of h (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _
      (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]) _ (by rw [hnb]; exact nbF_eq _ _ (hnb ▸ h.nb1)) rfl
  · have hLW : LiveSep L1 [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8)] :=
      liveSep_ext h.ext (fun r hr => by
          have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hout.of_sub (by omega) (by simp only; omega))
    have hWR : LiveSep [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8)] R.rt := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hout.of_sub (by omega) (by simp only; omega)
    refine wbCall (L1 := L1) (b1 := b1) hwb rfl ⟨?_, ?_, ?_, ?_, by omega, ?_, ?_⟩ (hsv.2.2.2.2.2.1 [2]) ?_ ?_ ?_
      fun buf junk f v m ex ep hfr hlf hsl hapL hapW hinvS => ?_
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · dsimp only; rw [hsp96]; omega
    · dsimp only; rw [hsp96]; omega
    · dsimp only; rw [hsp96]; omega
    · dsimp only; rw [hsp96, Memory.accessible_writeLE, Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hwS (by omega) (by omega)
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]; exact inv_hdr h
    · dsimp only; rw [hsp96]; exact hLW
    · dsimp only; rw [hsp96]; exact hWR
    dsimp only at hfr hlf hapW hinvS hsl hapL
    rw [hsp96] at hfr hapW
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28] at hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hacc16b : m.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hb8a : m.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
    have hb8b : m.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hacc16b (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hbz : buf.toNat + 16 ≤ z ∨ z + 32 ≤ buf.toNat := by
      rcases hzH1 with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hbS : buf.toNat + 16 ≤ s.sp.toNat - 4560 ∨ s.sp.toNat + 32 ≤ buf.toNat := by
      have := hbufR.apart hout; unfold Apart at this; omega
    have hrdS : ∀ a n, s.sp.toNat - 4560 ≤ a → a + n ≤ s.sp.toNat + 32 → (a + n ≤ s.sp.toNat - 4192 ∨
        s.sp.toNat - 104 ≤ a) → m.readLE a n = ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE a n := by
      intro a n h1 h2 h3
      exact hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega⟩)
    have hm87 : m.readLE (s.sp.toNat - 9) 1 = hNeg s.mem x := by
      rw [hrdS _ _ (by omega) (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hng
    have hmfp : m.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
      rw [hrdS _ _ (by omega) (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hfp
    have hmlr : m.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      rw [hrdS _ _ (by omega) (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hlr
    have hH16 : ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE (z + 16) 8 = l' := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    have hm16 : m.readLE (z + 16) 8 = l' := by
      rcases hzH1 with hL | hO
      · rw [hlf.readLE_nil _ _ (hL.sub (by omega) (by omega))]; exact hH16
      · rw [hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hO.of_sub (by omega) (by omega), by omega⟩)]; exact hH16
    have hmz : m.accessible z 32 true = true := by
      rw [hfr.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hzaS
    have hmS : m.accessible (s.sp.toNat - 4560) (4560 + 32) true = true := by
      rw [hfr.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hwS
    janus_run [hb8a, hb8b, hbuf64, hm87, hmfp, hmlr, hm16, hmz, hmS, hsp96]
    have hMw : MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c')
        ((m.writeLE buf.toNat 8 p').writeLE (buf.toNat + 8) 8 (S.mem.readLE (z + 8) 8))
        (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat - 104)]) :=
      ((hfr.mono fun a n ho => by
          simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; exact ⟨ho.1, by omega⟩).writeLE_inRanges
        _ ((hbufR.sub (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hbufR.sub (by omega) (by omega)).append_left _)
    have hLw : LiveFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c')
        ((m.writeLE buf.toNat 8 p').writeLE (buf.toNat + 8) 8 (S.mem.readLE (z + 8) 8)) L1 [] :=
      (hlf.writeLE _ (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))).writeLE _
        (Outside.of_sub hapL.outside (by omega) (by omega))
    have hIw : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1
        ((m.writeLE buf.toNat 8 p').writeLE (buf.toNat + 8) 8 (S.mem.readLE (z + 8) 8))) := by
      rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
        view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
      exact hinvS _ (by janus_frame)
    exact post_of h hMw hLw hIw _ (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]) _
      (by rw [hnb]; exact nbF_eq _ _ (hnb ▸ h.nb1)) rfl

end FvModexp.Arm64.IntAS
