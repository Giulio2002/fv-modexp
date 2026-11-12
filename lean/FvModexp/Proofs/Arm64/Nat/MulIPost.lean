import FvModexp.Proofs.Arm64.Nat.MulIRet

set_option autoImplicit false

/-!
# `(*Int).mul` (arm64): the postcondition `IPost` from `IR` and the header stores (int.go:201-203; pure)

After the inner call: `z.abs.len, cap := l', c'` (`STP` at `0x1b0d04`), the write barrier (on: `gcWriteBarrier2`, its two
buffer stores; memory `Mw`), `z.abs.ptr := p'`, `z.neg := len ≠ 0 && (x.neg ≠ y.neg)` (one byte). `ipost_of`: from `IR`
and these stores, `IPost`. (Adapted from `IntAS.post_of`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

/-- the sign of a product of signed magnitudes (`neg ∈ {0, 1}`) -/
theorem sgn_mul {nx ny : Nat} (X Y : Nat) (hx : nx ≤ 1) (hy : ny ≤ 1) :
    (if nx = 0 then (X : Int) else -(X : Int)) * (if ny = 0 then (Y : Int) else -(Y : Int)) =
      if nx ^^^ ny = 0 then ((X * Y : Nat) : Int) else -((X * Y : Nat) : Int) := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;>
    simp [Int.natCast_mul, Int.mul_neg, Int.neg_mul]

theorem xor_le_one {nx ny : Nat} (hx : nx ≤ 1) (hy : ny ≤ 1) : nx ^^^ ny ≤ 1 := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;> decide

/-- the frame lists of `IPost` / `ExactI`: the header `zr` plus `MPost`'s `pr :: sw` -/
theorem out_split {rt w sw : List (Nat × Nat)} {zr pr : Nat × Nat} {a n : Nat}
    (h : Outside a n (rt ++ w ++ [zr, pr] ++ sw)) : Outside a n (rt ++ w ++ [pr] ++ sw) ∧ Outside a n (rt ++ w ++ [zr]) := by
  obtain ⟨z1, z2⟩ := zr; obtain ⟨p1, p2⟩ := pr
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨⟨⟨hr, hw⟩, hz, hp⟩, hs⟩ := h
  exact ⟨⟨⟨⟨hr, hw⟩, hp⟩, hs⟩, ⟨hr, hw⟩, hz⟩

theorem out_split1 {sw : List (Nat × Nat)} {zr pr : Nat × Nat} {a n : Nat} (h : Outside a n ([zr, pr] ++ sw)) :
    Outside a n ([pr] ++ sw) := by
  obtain ⟨z1, z2⟩ := zr; obtain ⟨p1, p2⟩ := pr
  simp only [List.cons_append, List.nil_append, outside_cons] at h ⊢; exact h.2

theorem out_split2 {sw : List (Nat × Nat)} {zr pr : Nat × Nat} {a n : Nat} (h : Outside a n ([zr, pr] ++ sw)) :
    Outside a n [zr] := by
  obtain ⟨z1, z2⟩ := zr; obtain ⟨p1, p2⟩ := pr
  simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`IPost`** from `IR` and the stores after the inner call (see the module doc) -/
theorem ipost_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s : State}
    {p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : IR R b L W z st x y s p' l' c' b1 L1 S) {Mw : Memory}
    (hMw : MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') Mw
      (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat - 104)]))
    (hLw : LiveFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') Mw L1 [])
    (hIw : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 Mw))
    (s' : State) (nbF : Nat) (hnbF : nbF = if l' = 0 then 0 else hNeg s.mem x ^^^ hNeg s.mem y)
    (hm : s'.mem = (Mw.writeLE (z + 8) 8 p').writeLE z 1 nbF) :
    IPost R b L W z st x y s s' := by
  have hpre := h.pre
  obtain ⟨hce, hiw, -, -, -, -, ⟨hnx1, -⟩, ⟨hny1, -⟩, hza, hz48, hzo, hzH, -, -, -, -, hzst, -, hzarr,
    ⟨-, -, ⟨-, -, hzw, -, -, -⟩, -⟩, hstk, -, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨-, -, hstw, -⟩ := hstk
  have hW : 96 + 4608 ≤ W := by have := mulW_ge (hL s.mem x) (hL s.mem y); unfold imW at hiw; omega
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  have hzw' := hzw
  simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  have hc40 := h.c40; have hlc := h.lc
  have hnbF1 : nbF ≤ 1 := by
    rw [hnbF]; split
    · exact Nat.zero_le _
    · exact xor_le_one hnx1 hny1
  -- the frame of the stores after the call
  have hFH : MemFrame S.mem ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') [(z, z + 32)] := by janus_frame
  have hF2 : MemFrame Mw ((Mw.writeLE (z + 8) 8 p').writeLE z 1 nbF) [(z, z + 32)] := by janus_frame
  rw [← hm] at hF2
  have T : MemFrame S.mem s'.mem (R.rt ++ winA s W 40 ++ [(z, z + 32)]) :=
    MemFrame.trans (MemFrame.trans hFH hMw (rs'' := R.rt ++ winA s W 40 ++ [(z, z + 32)]) fun a n ho => by
        simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        obtain ⟨⟨hr, h1, -⟩, hz⟩ := ho
        exact ⟨hz, hr, by omega⟩) hF2 fun a n ho => by
      refine ⟨ho, ?_⟩
      simp only [outside_append] at ho; exact ho.2
  have TL : LiveFrame S.mem s'.mem L1 [(z, z + 32)] :=
    ((LiveFrame.mk fun a n _ ho => hFH.readLE a n ho).trans (LiveFrame.mono_ws hLw fun _ _ _ => trivial)
      fun _ _ hi => hi).trans (LiveFrame.mk fun a n _ ho => hF2.readLE a n ho) fun _ _ hi => hi
  have kp : ∀ a n, Held R L1 a n → Outside a n (winA s W 40) → Outside a n [(z, z + 32)] →
      s'.mem.readLE a n = S.mem.readLE a n := fun a n hH h1 h2 => Held.readLE2 hH T TL h1 h2
  -- `z`'s header in `Mw`
  have rdW : ∀ a n, z ≤ a → a + n ≤ z + 32 →
      Mw.readLE a n = ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE a n := by
    intro a n h1 h2
    rcases hzH1 with hi | ho
    · exact hLw.readLE_nil a n (hi.sub h1 h2)
    · exact hMw.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.of_sub h1 h2, by omega⟩)
  have eN : s'.mem.readLE z 1 = nbF := by
    rw [hm, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  have eP : s'.mem.readLE (z + 8) 8 = p' := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt h.p64
  have eL : s'.mem.readLE (z + 16) 8 = l' := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eC : s'.mem.readLE (z + 24) 8 = c' := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eN' : hNeg s'.mem z = nbF := eN
  have eP' : hP s'.mem z = p' := eP
  have eL' : hL s'.mem z = l' := eL
  have eC2 : hC s'.mem z = c' := eC
  -- the result array: outside the window, apart from `z`'s header, held in `L1`
  have parr : 0 < c' → Outside p' (8 * c') (winA s W 40) ∧ Apart p' (8 * c') z 32 := by
    intro hc
    rcases h.kind with ⟨rfl, rfl⟩ | hf
    · exact ⟨winA_of_win' hzw, (hzarr hc).2.2⟩
    · obtain ⟨-, hin, hap⟩ := hf hc
      refine ⟨?_, ?_⟩
      · have := NatAdd.outside_of_inRanges hout hin
        simp only [winA, outside_cons, outside_nil, and_true]; omega
      · rcases hzH with h1 | h1
        · have := hap.apart_of_inRanges h1; unfold Apart; omega
        · exact (hin.apart h1).symm
  have rdF : 0 < c' → ∀ a n, p' ≤ a → a + n ≤ p' + 8 * c' → s'.mem.readLE a n = S.mem.readLE a n := by
    intro hc a n h1 h2
    obtain ⟨hpo, hpz⟩ := parr hc
    unfold Apart at hpz
    exact kp a n ((h.live hc).2.1.sub h1 h2) (hpo.of_sub h1 h2) (by
      simp only [outside_cons, outside_nil, and_true]; omega)
  have eV : natVal s'.mem p' l' = natVal S.mem p' l' := by
    rcases Nat.eq_zero_or_pos l' with h0 | h0
    · subst h0; rfl
    · exact rdF (by omega) _ _ (Nat.le_refl _) (by omega)
  have eNorm : NatNorm s'.mem p' l' := by
    rcases h.norm with h1 | h1
    · exact Or.inl h1
    · rcases Nat.eq_zero_or_pos l' with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rw [rdF (by omega) _ _ (by omega) (by omega)]; exact h1)
  -- the stack header
  have hstH : Held R L1 st 24 := h.sb.1.1.2.1
  have hsk : ∀ k, k + 8 ≤ 24 → s'.mem.readLE (st + k) 8 = S.mem.readLE (st + k) 8 := fun k hk =>
    kp _ _ (hstH.sub (by omega) (by omega)) ((winA_of_win' hstw).of_sub (by omega) (by omega))
      (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hzst; omega)
  have sW : stW s'.mem st = stW S.mem st := by have := hsk 0 (by omega); simpa using this
  have sL : stLen s'.mem st = stLen S.mem st := hsk 8 (by omega)
  have sC : stCap s'.mem st = stCap S.mem st := hsk 16 (by omega)
  have hext := h.ext
  refine ⟨?_, by rw [eN']; exact hnbF1, ?_, ?_, ?_, ?_, ?_, ⟨L1, b1, hext, h.bud, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · -- the value
    have ei : intZ s'.mem z = if nbF = 0 then (natVal S.mem p' l' : Int) else -(natVal S.mem p' l' : Int) := by
      unfold intZ; rw [eN', eP', eL', eV]
    have exy : intZ s.mem x * intZ s.mem y = if hNeg s.mem x ^^^ hNeg s.mem y = 0 then
        ((natVal S.mem p' l' : Nat) : Int) else -((natVal S.mem p' l' : Nat) : Int) := by
      unfold intZ; rw [h.val]; exact sgn_mul _ _ hnx1 hny1
    rw [ei, exy, hnbF]
    rcases Nat.eq_zero_or_pos l' with h0 | h0
    · have hV : natVal S.mem p' l' = 0 := by rw [h0]; rfl
      simp [h0, hV]
    · have hl0 : l' ≠ 0 := by omega
      simp only [hl0, ↓reduceIte]
  · rw [eN', eL', hnbF]; split
    · intro h1; exact absurd h1 (by decide)
    · intro _; exact Nat.pos_of_ne_zero (by assumption)
  · rw [eP', eL']; exact eNorm
  · rw [eL', eC2]; exact hlc
  · rw [eL']; exact h.lxy
  · rw [eC2]; exact hc40
  · rw [hm, view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega))]
    exact hIw
  · rw [eP', eC2]
    intro hc
    obtain ⟨a1, a2, a3, a4⟩ := h.live hc
    exact ⟨a1, a2, by rw [T.accessible]; exact a3, a4⟩
  · rw [eP', eC2]; exact h.kind
  · simp only [hP, hC]; rw [eP, eC, sW, sC]; exact h.fa
  · -- `ExactI`
    rw [eP', eC2]
    intro h1 h2 h3
    obtain ⟨e1, e2, hvz, hF', hLF'⟩ := h.ex h1 h2 h3
    have eZ : natVal s'.mem (hP s.mem z) (hL s.mem x + hL s.mem y) =
        natVal S.mem (hP s.mem z) (hL s.mem x + hL s.mem y) := by
      rcases Nat.eq_zero_or_pos (hL s.mem x + hL s.mem y) with h0 | h0
      · rw [h0]; rfl
      · rw [← e1]; exact rdF (by omega) _ _ (Nat.le_refl _) (by omega)
    refine ⟨e1, e2, ?_, MemFrame.trans hF' T fun a n ho => out_split ho, ?_⟩
    · rw [eZ]
      rcases hvz with hv | ⟨h0, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨h0, hv⟩
    · exact (LiveFrame.mono_ws hLF' fun a n ho => out_split1 ho).trans (LiveFrame.mono_ws TL fun a n ho => out_split2 ho)
        fun _ _ hi => hext.inRanges_old hi
  · -- `StackBackL`
    obtain ⟨⟨sbok, sblen, sbor⟩, sbm⟩ := h.sb
    refine ⟨⟨stkOK_move sbok sW sL sC T.accessible, by rw [sL, sblen], ?_⟩, ArrIn.congr sbm sW sC fun _ h => h⟩
    rw [sW, sC]; exact sbor
  · exact MemFrame.trans h.mf T fun a n ho => out_split ho
  · exact (LiveFrame.mono_ws h.lf fun a n ho => out_split1 ho).trans (LiveFrame.mono_ws TL fun a n ho => out_split2 ho)
      fun _ _ hi => hext.inRanges_old hi

end FvModexp.Arm64.NatMul
