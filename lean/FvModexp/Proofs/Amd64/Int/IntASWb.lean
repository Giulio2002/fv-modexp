import FvModexp.Proofs.Amd64.Int.IntASPost

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): the memory after `gcWriteBarrier2` in the tail (pure)

At each of the three tails the barrier-on path stores `z.abs.len, cap`, pushes the return address `ra` at
`RSP₀ - 96` (`CALL`) and calls `gcWriteBarrier2` (window `[RSP₀ - 4192, RSP₀ - 88)`), then stores
`(new ptr, old ptr)` into the buffer. `wb_reads`: the facts the code after the call reads (spills, saved `BP`,
own return address, `z.abs.len`, accessibility, buffer placement). `wb_post`: the frames and the invariant for
`post_of` (write set `[RSP₀ - 4192, RSP₀ - 88)`). Small separate lemmas, so the tails' runs keep a small context.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.IntAS

/-- the memory after the header stores and the `CALL`'s return-address push -/
@[reducible] def mW (S : State) (z l' c' t ra : Nat) : Arm64.Memory :=
  ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').writeLE (t - 96) 8 ra

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem wb_reads {sub : Bool} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s : State}
    {nb V cost p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) (ra : Nat) {m' : Arm64.Memory} {buf : Nat}
    (hfr2 : MemFrame (mW S z l' c' (s.regs 4).toNat ra) m'
      (R.rt ++ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96)]))
    (hlf2 : LiveFrame (mW S z l' c' (s.regs 4).toNat ra) m' L1 [])
    (hsl : WbSlots R.rt m' buf 2) (hapL : ApartAll buf (8 * 2) L1) :
    m'.accessible buf 8 true = true ∧ m'.accessible (buf + 8) 8 true = true ∧ buf + 8 < 2 ^ 64 ∧
      (buf + 16 ≤ z ∨ z + 32 ≤ buf) ∧
      (buf + 16 ≤ (s.regs 4).toNat - 4536 ∨ (s.regs 4).toNat + 32 ≤ buf) ∧
      m'.readLE ((s.regs 4).toNat - 88 + 79) 1 = hNeg s.mem x ∧
      m'.readLE ((s.regs 4).toNat - 88 + 80) 8 = (s.regs 5).toNat ∧
      m'.readLE ((s.regs 4).toNat - 88 + 88) 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
      m'.readLE (z + 16) 8 = l' ∧ m'.accessible z 32 true = true ∧
      m'.accessible ((s.regs 4).toNat - 4536) (4536 + 32) true = true := by
  have hpre := h.pre
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩, -, -, -, -, hza, hz48, hzo, hzH, -⟩ := hpre
  try simp only [regSP] at hb' ha hw
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  have hlc := h.lc; have hc40 := h.c40
  obtain ⟨hsl1, hsl2, hsl3, -⟩ := hsl
  have hbufR : InRanges buf 16 R.rt := by simpa using hsl1
  have hacc16b : m'.accessible buf 16 true = true := by simpa using hsl3
  have hbz : buf + 16 ≤ z ∨ z + 32 ≤ buf := by
    rcases hzH1 with hL | hO
    · have := hapL.apart_of_inRanges hL; omega
    · have := hbufR.apart hO; unfold Apart at this; omega
  have hbS : buf + 16 ≤ (s.regs 4).toNat - 4536 ∨ (s.regs 4).toNat + 32 ≤ buf := by
    have := hbufR.apart hout; unfold Apart at this; omega
  -- reads of the caller's window outside the callee's
  have hrdS : ∀ a n, (s.regs 4).toNat - 4536 ≤ a → a + n ≤ (s.regs 4).toNat + 32 →
      (s.regs 4).toNat - 88 ≤ a → m'.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr2.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega⟩),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hH16 : (mW S z l' c' (s.regs 4).toNat ra).readLE (z + 16) 8 = l' := by
    simp only [mW]
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨Arm64.Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega),
    Arm64.Memory.accessible_mono _ hacc16b (by omega) (by omega), by omega, hbz, hbS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrdS _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
    exact h.ng
  · rw [hrdS _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
    exact h.mbp
  · rw [hrdS _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
    exact h.ra
  · rcases hzH1 with hL | hO
    · rw [hlf2.readLE _ _ (hL.sub (by omega) (by omega)) trivial]; exact hH16
    · rw [hfr2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hO.of_sub (by omega) (by omega), by omega⟩)]; exact hH16
  · rw [hfr2.accessible]; simp only [mW, Arm64.Memory.accessible_writeLE]; rw [h.mf.accessible]; exact hza
  · rw [hfr2.accessible]; simp only [mW, Arm64.Memory.accessible_writeLE]; rw [h.mf.accessible]; exact hw

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem wb_post {sub : Bool} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s : State}
    {nb V cost p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) (ra : Nat) {m' : Arm64.Memory} {buf : Nat}
    (hfr2 : MemFrame (mW S z l' c' (s.regs 4).toNat ra) m'
      (R.rt ++ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96)]))
    (hlf2 : LiveFrame (mW S z l' c' (s.regs 4).toNat ra) m' L1 [])
    (hsl : WbSlots R.rt m' buf 2) (hapL : ApartAll buf (8 * 2) L1)
    (hinvS : InvSlots R b1 L1 (s.regs 14).toNat R.rt m' buf 2) (v1 v2 : Nat) :
    MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2)
        (R.rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)]) ∧
      LiveFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2)
        L1 [] ∧
      R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2)) := by
  have hpre := h.pre
  obtain ⟨⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, hLs, -⟩, -⟩ := hpre
  try simp only [regSP] at hb'
  obtain ⟨hsl1, -, -, -⟩ := hsl
  have hbufR : InRanges buf 16 R.rt := by simpa using hsl1
  have hF1 : MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') (mW S z l' c' (s.regs 4).toNat ra)
      [((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by simp only [mW]; janus_frame
  have hLW : LiveSep L1 [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] :=
    liveSep_ext h.ext (fun r hr => by
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

end FvModexp.Amd64.IntAS
