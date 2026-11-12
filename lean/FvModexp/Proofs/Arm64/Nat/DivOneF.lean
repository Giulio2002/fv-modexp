import FvModexp.Proofs.Arm64.Nat.DivPostK
import FvModexp.Proofs.Arm64.Nat.DivRel

/-!
# `nat.div` (arm64), `len v = 1`: the postcondition from `AtW` and the `setWord` tail's facts (pure)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.NatDiv

/-- a held range outside the written ranges `ws` and `cs` keeps its bytes -/
theorem held_keep2 {R : RtInv} {L : List (Nat × Nat)} {M M' : Memory} {ws cs : List (Nat × Nat)} {a n : Nat}
    (hh : Held R L a n) (hLF : LiveFrame M M' L ws) (hMF : MemFrame M M' (R.rt ++ cs)) (hw : Outside a n ws)
    (hc : Outside a n cs) : M'.readLE a n = M.readLE a n := by
  rcases hh with hin | hout
  · exact hLF.readLE a n hin hw
  · exact hMF.readLE a n (by rw [outside_append]; exact ⟨hout, hc⟩)

/-- an object of a grown live set lies outside the window -/
theorem inL_out {R : RtInv} {L L' : List (Nat × Nat)} {s : State} (hce : CallEnv R L s 41504 112)
    (hext : LiveExt R L L') {a n : Nat} (hin : InRanges a n L') :
    a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a := by
  have hout := hce.2.2.2.1
  have hLs := hce.2.2.2.2.2.2.1
  obtain ⟨r, hr, i1, i2⟩ := hin
  obtain ⟨ns, rfl, hn, -⟩ := hext
  rcases List.mem_append.1 hr with hr | hr
  · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  · have := outside_of_inRanges hout (hn r hr).1; omega

theorem natLive_ext {R : RtInv} {L L' : List (Nat × Nat)} {m m' : Memory} {p c : Nat} (h : NatLive m R L p c)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) (hext : LiveExt R L L') : NatLive m' R L' p c :=
  fun hc => by
    obtain ⟨a1, a2, a3, a4⟩ := h hc
    exact ⟨a1, hext.held a2, by rw [hacc]; exact a3, a4⟩

/-- a frame inside the window (stack stores) gives the `setWord` tail's frame facts -/
theorem winFrame {R : RtInv} {L L' : List (Nat × Nat)} {s : State} (hce : CallEnv R L s 41504 112)
    (hext : LiveExt R L L') {M M' : Memory} {lo hi : Nat} (hF : MemFrame M M' [(lo, hi)])
    (hlo : s.sp.toNat - 41504 ≤ lo) (hhi : hi ≤ s.sp.toNat - 8) (z2 z2c : Nat) :
    MemFrame M M' (R.rt ++ winA s 41504 112 ++ ar z2 z2c) ∧ LiveFrame M M' L' (ar z2 z2c) := by
  refine ⟨hF.mono fun a n h => ?_, ⟨fun a n hin _ => hF.readLE a n ?_⟩⟩
  · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  · have := inL_out hce hext hin
    simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the postcondition of the `len v = 1` paths** -/
theorem oneFin {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul v : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v 1 s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L zp zc z2 z2c u ul v 1 s q ql qc L' b' T) (s' : State) {r rl rc : Nat}
    {L'' : List (Nat × Nat)} {b'' : Nat}
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 1 = BitVec.ofNat 64 ql) (h2 : s'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 3 = BitVec.ofNat 64 r) (h4 : s'.regs 4 = BitVec.ofNat 64 rl) (h5 : s'.regs 5 = BitVec.ofNat 64 rc)
    (hM : MemFrame T.mem s'.mem (R.rt ++ winA s 41504 112 ++ ar z2 z2c)) (hLF2 : LiveFrame T.mem s'.mem L' (ar z2 z2c))
    (hext2 : LiveExt R L' L'') (hb2 : b' - makeCost 1 ≤ b'')
    (hinv : R.inv b'' L'' (s.regs 28).toNat (view R.rt L'' s'.mem))
    (hr : ExpHyp.NatOF R L L'' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v 1)) :
    Post R b dc L zp zc st z2 z2c u ul v 1 s s' := by
  have hp := hpre.f
  have hout := hp.ce.2.2.2.1
  have hb' := hp.ce.2.1.2.1
  have hq := hW.hq
  obtain ⟨hv, hn, hnc, hc40, hlive, hror⟩ := hq
  -- `q`'s array is held in `L'`, outside the window and apart from `z2`'s array
  have hqo : 0 < qc → Outside q (8 * qc) (winA s 41504 112) ∧ Outside q (8 * qc) (ar z2 z2c) := by
    intro hqc
    rcases hror with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
    · have hw := (hp.zo.2.2 hqc).1
      simp only [win, outside_cons, outside_nil, and_true] at hw
      refine ⟨by simp only [winA, outside_cons, outside_nil, and_true]; omega, outside_ar fun hc => ?_⟩
      have := hp.zz2 hqc hc; unfold Apart at this; omega
    · have := outside_of_inRanges hout hin
      refine ⟨by simp only [winA, outside_cons, outside_nil, and_true]; omega, outside_ar fun hc => ?_⟩
      have := held_apart_fresh (hp.z2o.2.1 hc).2.1 hap hin
      unfold Apart at this; omega
  have hkeep : ∀ a n, q ≤ a → a + n ≤ q + 8 * qc → 0 < qc → s'.mem.readLE a n = T.mem.readLE a n := by
    intro a n h1 h2 hqc
    obtain ⟨o1, o2⟩ := hqo hqc
    have hM' : MemFrame T.mem s'.mem (R.rt ++ (winA s 41504 112 ++ ar z2 z2c)) := by
      rw [← List.append_assoc]; exact hM
    exact held_keep2 ((hlive hqc).2.1.sub h1 h2) hLF2 hM' (o2.of_sub h1 h2)
      (by rw [outside_append]; exact ⟨o1.of_sub h1 h2, o2.of_sub h1 h2⟩)
  have hq' : ExpHyp.NatOF R L L'' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v 1) := by
    refine ⟨?_, ?_, hnc, hc40, ?_, hror⟩
    · by_cases h0 : ql = 0
      · rw [h0] at hv ⊢; simpa [natVal] using hv
      · rw [← hv]; exact hkeep _ _ (Nat.le_refl _) (by omega) (by omega)
    · by_cases hq0 : ql = 0
      · exact Or.inl hq0
      · rcases hn with h | h
        · exact absurd h hq0
        · exact Or.inr (by rw [hkeep _ _ (by omega) (by omega) (by omega)]; exact h)
    · intro hqc
      obtain ⟨a1, a2, a3, a4⟩ := hlive hqc
      exact ⟨a1, hext2.held a2, by rw [hM.accessible]; exact a3, a4⟩
  refine post_kept hpre s' h0 h1 h2 h3 h4 h5 hq' hr (hW.ext.trans hext2) ?_ hinv
    (hW.mf.trans hM fun a n h => ?_) ⟨fun a n hin ho => ?_⟩
  · have h1 := hW.bud; have h2 := hp.cost; simp only [cost] at h2 ⊢; omega
  · simp only [outside_append] at h ⊢; exact ⟨h.1, ⟨h.1.1, h.2⟩⟩
  · rw [outside_append] at ho
    rw [hLF2.readLE a n (hW.ext.inRanges_old hin) ho.2]
    exact hW.lf.readLE a n hin ho.1

end FvModexp.Arm64.NatDiv
