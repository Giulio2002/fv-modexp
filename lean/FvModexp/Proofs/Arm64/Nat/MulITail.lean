import FvModexp.Proofs.Arm64.Nat.MulIPost

set_option autoImplicit false

/-!
# `(*Int).mul` (arm64): from the return `0x1b0d00` of the inner `nat.mul` call to `RET` (int.go:201-203)

`z.abs.len, cap` stores (`STP` at `0x1b0d04`), the write-barrier flag test (on: `gcWriteBarrier2` and its buffer stores),
`z.abs.ptr` store, `z.neg = len ≠ 0 && x.neg ^ y.neg` (the sign bytes re-read through the spilled `x`, `y`), epilogue.
(Adapted from `IntAS.tail`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA wbCall liveSep_ext)

/-- the invariant after the header stores `len, cap` -/
theorem IR.inv_hdr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s : State}
    {p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State} (h : IR R b L W z st x y s p' l' c' b1 L1 S) :
    R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c')) := by
  have hzH1 : Held R L1 z 32 := h.ext.held h.pre.2.2.2.2.2.2.2.2.2.2.2.1
  rw [view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega))]
  exact h.inv

/-- the final sign byte -/
theorem nbF_mul {l' nx ny : Nat} (hx : nx ≤ 1) (hy : ny ≤ 1) (hl : l' ≠ 0) :
    (BitVec.ofNat 64 nx ^^^ BitVec.ofNat 64 ny).toNat = if l' = 0 then 0 else nx ^^^ ny := by
  rw [if_neg hl, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem itail (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibMul.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (W z st x y : Nat) (s : State)
    (p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (h : IR R b L W z st x y s p' l' c' b1 L1 S) (hpc : S.pc = BitVec.ofNat 64 0x1b0d00) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' => Kept s s' ∧ IPost R b L W z st x y s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, hiw, hsv, -, -, -,
    ⟨hnx1, hxa, hx48, hxo, -⟩, ⟨hny1, hya, hy48, hyo, -⟩, hza, hz48, hzo, hzH, hzg, hzwb, hzx, hzy, -, hwbf, -, -, -,
    -, -⟩ := hpre
  have hW4 : 4704 ≤ W := Nat.le_trans (Nat.add_le_add_right (mulW_ge _ _) 96) hiw
  have hsp := h.sp; have h28 := h.r28; have h29 := h.r29; have h18 := h.r18
  have h0 := h.r0; have h1 := h.r1; have h2 := h.r2
  have hzs := h.zs; have hxs := h.xs; have hys := h.ys; have hfp := h.fp; have hlr := h.lr
  have hnx := h.nx; have hny := h.ny
  have hc40 := h.c40; have hlc := h.lc; have hp64 := h.p64; have hlr4 := h.lr4; have hlr48 := h.lr48
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  unfold Apart at hzg hzwb hzx hzy
  have hwbv : wbA = 7616064 := rfl
  rw [hwbv] at hzwb
  have hsp96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hzaS : S.mem.accessible z 32 true = true := by rw [h.mf.accessible]; exact hza
  have hxaS : S.mem.accessible x 32 false = true := by rw [h.mf.accessible]; exact hxa
  have hyaS : S.mem.accessible y 32 false = true := by rw [h.mf.accessible]; exact hya
  have hwbS : S.mem.accessible wbA 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hwS : S.mem.accessible (s.sp.toNat - W) (W + 40) true = true := by rw [h.mf.accessible]; exact hw
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  janus_run [hsp, hsp96, hzs, hxs, hys, hfp, hlr, hnx, hny, hzaS, hxaS, hyaS, hwbS, hwS] until [cA "runtime.gcWriteBarrier2"]
  · obtain rfl : l' = 0 := by janus_assumption
    refine ⟨⟨rfl, ?_, ?_, ?_⟩, ipost_of h (MemFrame.refl _ _) (LiveFrame.refl _ _ _) h.inv_hdr _ 0 (by simp) rfl⟩
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
  · refine ⟨⟨rfl, ?_, ?_, ?_⟩, ipost_of h (MemFrame.refl _ _) (LiveFrame.refl _ _ _) h.inv_hdr _ _
      (by rw [if_neg (by janus_assumption)]) rfl⟩
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
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
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]; exact h.inv_hdr
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
    have hbH : ∀ a, Held R L1 a 32 → buf.toNat + 16 ≤ a ∨ a + 32 ≤ buf.toNat := by
      intro a hH
      rcases hH with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hbz := hbH z hzH1
    have hxH1 : Held R L1 x 32 := h.ext.held h.pre.2.2.2.2.2.2.1.2.2.2.2.1
    have hyH1 : Held R L1 y 32 := h.ext.held h.pre.2.2.2.2.2.2.2.1.2.2.2.2.1
    have hbx := hbH x hxH1
    have hby := hbH y hyH1
    have hbS : buf.toNat + 16 ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ buf.toNat := by
      have := hbufR.apart hout; unfold Apart at this; omega
    have hrdS : ∀ a n, s.sp.toNat - W ≤ a → a + n ≤ s.sp.toNat + 40 → (a + n ≤ s.sp.toNat - 4192 ∨
        s.sp.toNat - 104 ≤ a) → m.readLE a n = ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE a n := by
      intro a n h1 h2 h3
      exact hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega⟩)
    have hrdH : ∀ a, Held R L1 a 32 → (a + 32 ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ a) →
        m.readLE a 1 = ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE a 1 := by
      intro a hH ho
      rcases hH with hL | hO
      · exact hlf.readLE_nil _ _ (hL.sub (Nat.le_refl _) (by omega))
      · exact hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hO.of_sub (Nat.le_refl _) (by omega), by omega⟩)
    have hmx : m.readLE x 1 = hNeg s.mem x := by
      rw [hrdH x hxH1 hxo, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hnx
    have hmy : m.readLE y 1 = hNeg s.mem y := by
      rw [hrdH y hyH1 hyo, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hny
    have hmrd : ∀ a, (s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 88) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 40) →
        m.readLE a 8 = S.mem.readLE a 8 := by
      intro a ha'
      rw [hrdS _ _ (by omega) (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have hmfp : m.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := (hmrd _ (Or.inl (by omega))).trans hfp
    have hmlr : m.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := (hmrd _ (Or.inl (by omega))).trans hlr
    have hmxs : m.readLE (s.sp.toNat + 24) 8 = x := (hmrd _ (Or.inr (by omega))).trans hxs
    have hmys : m.readLE (s.sp.toNat + 32) 8 = y := (hmrd _ (Or.inr (by omega))).trans hys
    have hmz : m.accessible z 32 true = true := by
      rw [hfr.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hzaS
    have hmxa : m.accessible x 32 false = true := by
      rw [hfr.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hxaS
    have hmya : m.accessible y 32 false = true := by
      rw [hfr.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hyaS
    have hmS : m.accessible (s.sp.toNat - W) (W + 40) true = true := by
      rw [hfr.accessible, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hwS
    janus_run [hb8a, hb8b, hbuf64, hmx, hmy, hmfp, hmlr, hmxs, hmys, hmz, hmxa, hmya, hmS, hsp96]
    all_goals
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
    · refine ⟨⟨rfl, ?_, ?_, ?_⟩, ipost_of h hMw hLw hIw _ 0 (by rw [if_pos (by janus_assumption)]) rfl⟩
      · simp only [setReg_apply, wbRegs_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
      · simp only [setReg_apply, wbRegs_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
    · refine ⟨⟨rfl, ?_, ?_, ?_⟩, ipost_of h hMw hLw hIw _ _ (by rw [if_neg (by janus_assumption)]) rfl⟩
      · simp only [setReg_apply, wbRegs_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
      · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
      · simp only [setReg_apply, wbRegs_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18

end FvModexp.Arm64.NatMul
