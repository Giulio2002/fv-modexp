import FvModexp.Proofs.Arm64.Nat.MulOps

/-!
# The mul SCC (arm64): `MPre` one frame down, `MPost` one frame up

`mpre_down`: the caller's `MPre` (window `W`) gives the callee's `MPre` at `S1` (`SP - f`, window `W1`, memory
changed in the caller's window only), for the same or the swapped operands (`Ops.swap`). `mpost_up`: the callee's
`MPost` (from `S1` to `s2`) and window-only stores until the caller's return `s'` give the caller's `MPost`;
`mpost_comm`: `MPost` with the operands swapped.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep stkOK_frame outside_of_liveSep apart_of_apartAll)

theorem winA_sub {s S1 : State} {W W1 f : Nat} (hsp : S1.sp.toNat = s.sp.toNat - f) (hk : f + W1 ≤ W)
    (hf : 96 ≤ f) (hW : W ≤ s.sp.toNat) :
    ∀ a n, Outside a n (winA s W 88) → Outside a n (winA S1 W1 88) := by
  intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega

set_option maxRecDepth 20000 in
/-- `MPre` at a callee `f ≥ 96` bytes down (window `W1`), memory changed in the caller's window only -/
theorem mpre_down {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s S1 : State}
    {f W1 : Nat} (hpre : MPre R b L W zp zc st xp xl xc yp yl yc s)
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hg : S1.regs 28 = s.regs 28) (hF : MemFrame s.mem S1.mem (winA s W 88))
    (hreg : S1.mem.regions = s.mem.regions) (hk : f + W1 ≤ W) (hf : 96 ≤ f) (hf16 : f % 16 = 0)
    (hw1 : mulW xl yl ≤ W1) :
    MPre R b L W1 zp zc st xp xl xc yp yl yc S1 := by
  obtain ⟨hce, -, hsv, hglb, hty, hops, hstk, hcost, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce'
  have hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W 88) := hF.mono fun a n h => by
    simp only [outside_append] at h; exact h.2
  have hLF : LiveFrame s.mem S1.mem L [] := lf_win' [] hF hLs
  have hsub := win_sub (ab := 88) hsp hk (by omega) (by omega) (stk1 := W1) (above1 := 88)
  obtain ⟨eW, eL, eC⟩ := hdr_keep hstk.2.1 hstk.2.2.1 hF1 hLF
  refine ⟨callEnv_shift hce hLs hF1 hsp hg hreg hk (by omega) (by omega) hf16, hw1, hsv,
    globals_shift hglb hF1 (fun a n h => winA_of_win' h) hsub, hty, ?_, stkPre_shift hstk hF1 hLF hg hsub,
    by rw [eL]; exact hcost, ?_⟩
  · rw [hg]; exact (hops.mono hsub).move eW eL eC hF.accessible
  · rw [hg]; exact inv_frame_winA hF hout (by omega) (by decide) hinv

/-- a window-only frame chain around a callee frame -/
theorem frame3 {m0 m1 m2 m3 : Memory} {wa rs : List (Nat × Nat)} (h1 : MemFrame m0 m1 wa)
    (h2 : MemFrame m1 m2 rs) (h3 : MemFrame m2 m3 wa) {rs' : List (Nat × Nat)}
    (hs : ∀ a n, Outside a n rs' → Outside a n wa ∧ Outside a n rs) : MemFrame m0 m3 rs' :=
  MemFrame.trans (MemFrame.trans h1 h2 (rs'' := rs') hs) h3 fun a n h => ⟨h, (hs a n h).1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`MPost` one frame up**: the callee's `MPost` (`S1 → s2`, window `W1` at `SP - f`) with window-only stores
before (`s → S1`) and after (`s2 → s'`) is the caller's `MPost` (window `W`) -/
theorem mpost_up {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat}
    {s S1 s2 s' : State} {f W1 : Nat} (hpre : MPre R b L W zp zc st xp xl xc yp yl yc s)
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hk : f + W1 ≤ W) (hf : 96 ≤ f) (hg : S1.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S1.mem (winA s W 88))
    (hQ : MPost R b L W1 zp zc st xp xl xc yp yl yc S1 s2)
    (F3 : MemFrame s2.mem s'.mem (winA s W 88))
    (r0 : s'.regs 0 = s2.regs 0) (r1 : s'.regs 1 = s2.regs 1) (r2 : s'.regs 2 = s2.regs 2) :
    MPost R b L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hce, -, -, -, -, ⟨⟨-, -, -, -, -, hxw⟩, ⟨-, -, -, -, -, hyw⟩, ⟨-, -, hzw, -, -, -⟩, -⟩, hstk, -, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  obtain ⟨-, -, hstw, -⟩ := hstk
  have hsubA := winA_sub hsp hk hf (by omega)
  have hstA := winA_of_win' hstw
  obtain ⟨eW, eL, eC⟩ := hdr_frame hF hstA
  obtain ⟨eW3, eL3, eC3⟩ := hdr_frame F3 hstA
  have hxS : natVal S1.mem xp xl = natVal s.mem xp xl := by
    rcases Nat.eq_zero_or_pos xl with h0 | h0
    · subst h0; simp
    · exact natVal_frame hF (winA_of_win' (hxw h0).1)
  have hyS : natVal S1.mem yp yl = natVal s.mem yp yl := by
    rcases Nat.eq_zero_or_pos yl with h0 | h0
    · subst h0; simp
    · exact natVal_frame hF (winA_of_win' (hyw h0).1)
  obtain ⟨p', l', c', q0, q1, q2, hv, hn, hlc, hll, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex, hsb,
    hMF, hLF⟩ := hQ
  have hzA := winA_of_win' hzw
  have hpo : 0 < c' → Outside p' (8 * c') (winA s W 88) := by
    intro hc
    rcases hkind with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · exact hzA
    · have := NatAdd.outside_of_inRanges hout hin
      simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hwS : stkWs S1.mem st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  rw [hwS] at hMF hLF
  rw [hxS, hyS] at hv hex
  rw [eL] at hbud
  have hLs' : LiveSep L (win s W 88) := hLs
  have hFL : MemFrame s.mem s'.mem (R.rt ++ winA s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
    frame3 hF hMF F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨⟨h.1.1.1, hsubA _ _ h.1.1.2⟩, h.1.2⟩, h.2⟩
  have hLL : ∀ ws : List (Nat × Nat), LiveFrame S1.mem s2.mem L ws → LiveFrame s.mem s'.mem L ws := fun ws h =>
    LiveFrame.trans (LiveFrame.trans (lf_win' _ hF hLs') h fun _ _ h => h) (lf_win' _ F3 hLs') fun _ _ h => h
  refine ⟨p', l', c', by rw [r0, q0], by rw [r1, q1], by rw [r2, q2], ?_, ?_, hlc, hll, hc40, L', b', hext, hbud,
    inv_frame_winA F3 hout (by omega) (by decide) (by rw [← hg]; exact hinv), ?_, hkind, ?_, ?_, ?_, hFL, hLL _ hLF⟩
  · rcases Nat.eq_zero_or_pos l' with h0 | h0
    · subst h0; rw [natVal_zero, ← hv, natVal_zero]
    · rw [natVal_frame F3 ((hpo (by omega)).of_sub (Nat.le_refl _) (by omega)), hv]
  · rcases hn with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos l' with h0 | h0
      · exact Or.inl h0
      right; rw [F3.readLE _ _ ((hpo (by omega)).of_sub (by omega) (by omega))]; exact h
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hlive hc; exact ⟨a1, a2, by rw [F3.accessible]; exact a3, a4⟩
  · intro hne hc0 hcap0; rw [eC3] at hcap0; rw [eW3, eC3]; exact hfa hne hc0 hcap0
  · intro h1 h2 h3
    obtain ⟨e1, e2, hvz, hF', hLF'⟩ := hex h1 h2 h3
    rw [hwS] at hF' hLF'
    have hzN : Outside zp (8 * (xl + yl)) (winA s W 88) := hzA.of_sub (Nat.le_refl _) (by omega)
    refine ⟨e1, e2, ?_, frame3 hF hF' F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨⟨h.1.1.1, hsubA _ _ h.1.1.2⟩, h.1.2⟩, h.2⟩, hLL _ hLF'⟩
    rw [natVal_frame F3 hzN]
    rcases hvz with h | ⟨h0, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, by rw [h, natVal_frame hF hzN]⟩
  · obtain ⟨⟨sbok, sblen, sbor⟩, sbm⟩ := hsb
    refine ⟨⟨stkOK_frame sbok F3 hstA, by rw [eL3, sblen, eL], ?_⟩, ?_⟩
    · rw [eW3, eC3]
      rcases sbor with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by rw [h1, eW], by rw [h2, eC]⟩
      · exact Or.inr h
    · unfold ArrIn; rw [eW3, eC3]; intro hn'; apply sbm; rw [eW, eC]; exact hn'

set_option maxRecDepth 20000 in
/-- a callee called at `SP - f` with a frame `R.rt ++ winA S1 W1 88 ++ [z] ++ stkWs` (an inner `nat.mul`) keeps the
caller's frame outside the callee's window: the saved `FP`/`LR` slots `[S1.sp - 8, S1.sp + 8)` and the upper part
`[S1.sp + 88, SP + 88)` -/
theorem mul_keeps {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat}
    {s S1 : State} {m2 : Memory} {f W1 zp' zc' : Nat} (hpre : MPre R b L W zp zc st xp xl xc yp yl yc s)
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hk : f + W1 ≤ W) (hf : 96 ≤ f) (hW1 : 96 ≤ W1)
    (hF : MemFrame s.mem S1.mem (winA s W 88)) (hz' : Outside zp' (8 * zc') (win s W 88))
    (hMF : MemFrame S1.mem m2 (R.rt ++ winA S1 W1 88 ++ [(zp', zp' + 8 * zc')] ++ stkWs S1.mem st)) :
    ∀ a n, (S1.sp.toNat - 8 ≤ a ∧ a + n ≤ S1.sp.toNat + 8) ∨ (S1.sp.toNat + 88 ≤ a ∧ a + n ≤ s.sp.toNat + 88) →
      m2.readLE a n = S1.mem.readLE a n := by
  obtain ⟨hce, -, -, -, -, -, hstk, -, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨-, -, hstw, -, -, -, hfw, -⟩ := hstk
  obtain ⟨eW, eL, eC⟩ := hdr_frame hF (winA_of_win' hstw)
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw hz'
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  intro a n h
  refine hMF.readLE _ _ ?_
  simp only [stkWs, winA, outside_append, outside_cons, outside_nil, and_true]
  rw [eW, eL, eC]
  exact ⟨⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩, by omega, by omega⟩

end FvModexp.Arm64.NatMul
