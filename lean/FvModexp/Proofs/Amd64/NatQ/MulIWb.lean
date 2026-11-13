import FvModexp.Proofs.Amd64.NatQ.MulIPost

set_option autoImplicit false

/-!
# [amd64 twin (divmc s54) of Amd64/Int/IntASWb.lean, over `IR`] `(*Int).mul` (amd64): the memory after `gcWriteBarrier2` in the tail (pure)

After the inner `nat.mul` (`IR` at `0x5e2aa6`, `RSP = s - 88`) the barrier-on path stores `z.abs.len, cap`, pushes the
return address at `s - 96` (`CALL`) and calls `gcWriteBarrier2` (window `[s - 4192, s - 96)`), then stores
`(new ptr, old ptr)` into the buffer. `IR.inv_hdr`: the invariant after the header stores. `wbm_reads`: the facts the
code after the call reads (spills `x`, `y`, saved `BP`, own return address, the operands' sign bytes, accessibility,
buffer placement). `wbm_post`: the frames and the invariant for `ipost_of` (write set `[s - 4192, s - 88)`). Small
separate lemmas, so the tail's run keeps a small context.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.IntAS (hNeg hP hL hC wbA)

/-- the memory after the header stores and the `CALL`'s return-address push -/
@[reducible] def mWI (S : State) (z l' c' t ra : Nat) : Arm64.Memory :=
  ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').writeLE (t - 96) 8 ra

theorem liveSep_extI {R : RtInv} {L L1 : List (Nat × Nat)} (h : LiveExt R L L1) {w : List (Nat × Nat)}
    (hL : LiveSep L w) (hw : LiveSep w R.rt) : LiveSep L1 w := by
  obtain ⟨ns, rfl, hn, -⟩ := h
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hL r hr
  · obtain ⟨hin, -⟩ := hn r hr
    refine outside_of_forall fun q hq => ?_
    have := (hw q hq)
    obtain ⟨t, ht, t1, t2⟩ := hin
    have := MemFrame.outside_mem this ht
    omega

/-- the invariant after the header stores `len, cap` -/
theorem IR.inv_hdr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s : State}
    {p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State} (h : IR R b H L W z st x y s p' l' c' b1 L1 S) :
    R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c')) := by
  have hzH1 : Held R L1 z 32 := h.ext.held h.pre.2.2.2.2.2.2.2.2.2.2.2.1
  rw [view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega))]
  exact h.inv

theorem IR.w4704 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s : State}
    {p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State} (h : IR R b H L W z st x y s p' l' c' b1 L1 S) :
    4704 ≤ W :=
  Nat.le_trans (Nat.add_le_add_right (mulW64_ge (hL s.mem x) (hL s.mem y)) 96) h.pre.2.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem wbm_reads {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s : State}
    {p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : IR R b H L W z st x y s p' l' c' b1 L1 S) (ra : Nat) {m' : Arm64.Memory} {buf : Nat}
    (hfr2 : MemFrame (mWI S z l' c' (s.regs 4).toNat ra) m'
      (R.rt ++ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96)]))
    (hlf2 : LiveFrame (mWI S z l' c' (s.regs 4).toNat ra) m' L1 [])
    (hsl : WbSlots R.rt m' buf 2) (hapL : ApartAll buf (8 * 2) L1) :
    m'.accessible buf 8 true = true ∧ m'.accessible (buf + 8) 8 true = true ∧ buf + 8 < 2 ^ 64 ∧
      (buf + 16 ≤ z ∨ z + 32 ≤ buf) ∧ (buf + 16 ≤ x ∨ x + 32 ≤ buf) ∧ (buf + 16 ≤ y ∨ y + 32 ≤ buf) ∧
      (buf + 16 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 40 ≤ buf) ∧
      m'.readLE x 1 = hNeg s.mem x ∧ m'.readLE y 1 = hNeg s.mem y ∧
      m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
      m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
      m'.readLE ((s.regs 4).toNat + 24) 8 = x ∧ m'.readLE ((s.regs 4).toNat + 32) 8 = y ∧
      m'.accessible z 32 true = true ∧ m'.accessible x 32 false = true ∧ m'.accessible y 32 false = true ∧
      m'.accessible ((s.regs 4).toNat - W) (W + 40) true = true := by
  have hW4 := h.w4704
  have hpre := h.pre
  obtain ⟨⟨-, ⟨hb', -, hw⟩, -, -, hout, -⟩, -, -, -, -, -, ⟨-, hxa, -, hxo, hxH, -⟩, ⟨-, hya, -, hyo, hyH, -⟩,
    hza, -, hzo, hzH, -, -, -, hzx, hzy, -⟩ := hpre
  try simp only [regSP] at hb' hw
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  unfold Apart at hzx hzy
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  have hxH1 : Held R L1 x 32 := h.ext.held hxH
  have hyH1 : Held R L1 y 32 := h.ext.held hyH
  obtain ⟨hsl1, hsl2, hsl3, -⟩ := hsl
  have hbufR : InRanges buf 16 R.rt := by simpa using hsl1
  have hacc16b : m'.accessible buf 16 true = true := by simpa using hsl3
  have hbH : ∀ a, Held R L1 a 32 → buf + 16 ≤ a ∨ a + 32 ≤ buf := by
    intro a hH
    rcases hH with hL | hO
    · have := hapL.apart_of_inRanges hL; omega
    · have := hbufR.apart hO; unfold Apart at this; omega
  have hbS : buf + 16 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 40 ≤ buf := by
    have := hbufR.apart hout; unfold Apart at this; omega
  -- reads of the caller's window outside the callee's
  have hrdS : ∀ a n, (s.regs 4).toNat - W ≤ a → a + n ≤ (s.regs 4).toNat + 40 →
      (s.regs 4).toNat - 88 ≤ a → m'.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr2.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega⟩),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  -- a held operand's sign byte
  have hrdH : ∀ a, Held R L1 a 32 → (a + 32 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 40 ≤ a) →
      (a + 32 ≤ z ∨ z + 32 ≤ a) → m'.readLE a 1 = S.mem.readLE a 1 := by
    intro a hH ho hz
    have e : (mWI S z l' c' (s.regs 4).toNat ra).readLE a 1 = S.mem.readLE a 1 := by
      simp only [mWI]
      rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rcases hH with hL | hO
    · rw [hlf2.readLE _ _ (hL.sub (Nat.le_refl _) (by omega)) trivial]; exact e
    · rw [hfr2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hO.of_sub (Nat.le_refl _) (by omega), by omega⟩)]; exact e
  have hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w →
      m'.accessible a n w = s.mem.accessible a n w := by
    intro a n w e
    rw [hfr2.accessible]; simp only [mWI, Arm64.Memory.accessible_writeLE]; exact e
  refine ⟨Arm64.Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega),
    Arm64.Memory.accessible_mono _ hacc16b (by omega) (by omega), by omega, hbH z hzH1, hbH x hxH1, hbH y hyH1, hbS,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrdH x hxH1 hxo (by omega)]; exact h.nx
  · rw [hrdH y hyH1 hyo (by omega)]; exact h.ny
  · rw [hrdS _ _ (by omega) (by omega) (by omega)]; exact h.mbp
  · rw [hrdS _ _ (by omega) (by omega) (by omega)]; exact h.ra
  · rw [hrdS _ _ (by omega) (by omega) (by omega)]; exact h.xs
  · rw [hrdS _ _ (by omega) (by omega) (by omega)]; exact h.ys
  · rw [hacc _ _ _ (h.mf.accessible _ _ _)]; exact hza
  · rw [hacc _ _ _ (h.mf.accessible _ _ _)]; exact hxa
  · rw [hacc _ _ _ (h.mf.accessible _ _ _)]; exact hya
  · rw [hacc _ _ _ (h.mf.accessible _ _ _)]; exact hw

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem wbm_post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s : State}
    {p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : IR R b H L W z st x y s p' l' c' b1 L1 S) (ra : Nat) {m' : Arm64.Memory} {buf : Nat}
    (hfr2 : MemFrame (mWI S z l' c' (s.regs 4).toNat ra) m'
      (R.rt ++ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96)]))
    (hlf2 : LiveFrame (mWI S z l' c' (s.regs 4).toNat ra) m' L1 [])
    (hsl : WbSlots R.rt m' buf 2) (hapL : ApartAll buf (8 * 2) L1)
    (hinvS : InvSlots R b1 L1 (s.regs 14).toNat R.rt m' buf 2) (v1 v2 : Nat) :
    MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2)
        (R.rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)]) ∧
      LiveFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2)
        L1 [] ∧
      R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2)) := by
  have hW4 := h.w4704
  have hpre := h.pre
  obtain ⟨⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, hLs, -⟩, -⟩ := hpre
  try simp only [regSP] at hb'
  obtain ⟨hsl1, -, -, -⟩ := hsl
  have hbufR : InRanges buf 16 R.rt := by simpa using hsl1
  have hF1 : MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') (mWI S z l' c' (s.regs 4).toNat ra)
      [((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by simp only [mWI]; janus_frame
  have hLW : LiveSep L1 [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] :=
    liveSep_extI h.ext (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hout.of_sub (by omega) (by simp only; omega))
  refine ⟨?_, ?_, ?_⟩
  · exact ((MemFrame.trans hF1 hfr2 fun a n ho => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨by omega, ho.1, by omega⟩).writeLE_inRanges _
      ((hbufR.sub (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
      ((hbufR.sub (by omega) (by omega)).append_left _)
  · refine ⟨fun a n hin _ => ?_⟩
    have hap := hapL.apart_of_inRanges hin
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hlf2.readLE a n hin trivial, hF1.readLE a n ?_]
    obtain ⟨r, hr, h1, h2⟩ := hin
    have h3 := hLW r hr
    simp only [outside_cons, outside_nil, and_true] at h3 ⊢
    omega
  · rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
      view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
    exact hinvS _ (by janus_frame)

end FvModexp.Amd64.Q.NatMul
