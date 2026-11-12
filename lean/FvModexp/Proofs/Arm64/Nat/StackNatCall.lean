import FvModexp.Proofs.Arm64.Nat.StackNatN

/-!
# `(*stack).nat` (arm64): the preconditions of the `growslice` and `memclrNoHeapPointers` calls of `slices.Grow`
(pure lemmas about an abstract call state; janus_run's call closer is too slow on these contracts: > 6 min)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

/-- `type:big.Word` (growslice's element type) -/
abbrev wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

theorem wT_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE wT 8 = 8 ∧ m.readLE (wT + 8) 8 = 0 ∧ m.accessible wT 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

set_option maxRecDepth 20000 in
/-- the `growslice(w, len + nr, cap, len + nr - cap, Word)` call from `(*stack).nat`'s frame -/
theorem gcall_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State}
    (hpre : Pre R b L 4208 24 st n s) (hk : stCap s.mem st < stLen s.mem st + rnd n) (S : State)
    (hF : MemFrame s.mem S.mem [(s.sp.toNat - 4208, s.sp.toNat + 24)]) (hsp : S.sp.toNat + 112 = s.sp.toNat)
    (h28 : S.regs 28 = s.regs 28) (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (h0 : (S.regs 0).toNat = stW s.mem st) (h1 : (S.regs 1).toNat = stLen s.mem st + rnd n)
    (h2 : (S.regs 2).toNat = stCap s.mem st) (h3 : (S.regs 3).toNat = stLen s.mem st + rnd n - stCap s.mem st)
    (h4 : (S.regs 4).toNat = wT) :
    GrowslicePre 4096 S ∧ StackRoom S 4096 5 ∧
      LiveAt R (cA "runtime.growslice") (growsliceArgs S) L b (growsliceRound S) (S.regs 28).toNat S.mem
        (calleeStack S 4096 5) := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n ≤ n + 3 := by simp only [rnd]; omega
  have hwT : Apart wT 16 (s.sp.toNat - 4208) (4208 + 24) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hga hwT
  obtain ⟨ht1, ht2, ht3⟩ := wT_facts hd
  have hwTv : wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3 hwT h4
  have hgo : Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4208, s.sp.toNat + 24) :: R.rt) := by
    simp only [outside_cons]; exact ⟨by omega, hgr⟩
  have hround : growsliceRound S = 8 * growCap8 (stLen s.mem st + rnd n) (stCap s.mem st) := by
    simp only [growsliceRound, h1, h2]
  have hFr : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)]) :=
    hF.mono fun a k h => by rw [outside_append] at h; exact h.2
  have hc := call_pre R L b (growsliceRound S) (cA "runtime.growslice") (growsliceArgs S)
    (s := s) (S := S) (lo := s.sp.toNat - 4208) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 5) (fr := 112)
    hg1 hg2 (by omega) hgo hFr h28 hsp (by rw [← hsp] at hal; omega) h30a h30b (by decide) (by omega) (by omega)
    (by omega) ha (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4208) = 4208 + 24 by omega]; exact hw)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp only; rw [show s.sp.toNat + 24 - (s.sp.toNat - 4208) = 4208 + 24 by omega]; exact hout) hLs
    (by simp only [growsliceArgs, h0, h1, h2, h3, h4]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega))
    (by rw [h28]; exact RtInv.inv_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only; rw [show s.sp.toNat + 24 - (s.sp.toNat - 4208) = 4208 + 24 by omega]; exact hout) hinv0)
    (by rw [hround]; exact Nat.le_trans (growRound_le_cost _ _ _ hk) hcost)
  refine ⟨⟨⟨hc.1, ?_, ?_, ?_, by omega, by omega, by omega, by omega, ?_⟩, fun hp => ?_⟩, hc.2⟩
  · rw [h4]; exact ⟨by omega, by rw [hF.accessible]; exact ht3⟩
  · simp only [typSize, h4]; rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact ht1
  · simp only [typPtrBytes, h4]; rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact ht2
  · -- v0.3.1: the type descriptor (rodata) is outside the callee's window
    rw [h4]; simp only [calleeStack, outside_cons, outside_nil, and_true]; omega
  · have e : (S.regs 1).toNat - (S.regs 3).toNat = stCap s.mem st := by omega
    unfold GrowsliceOld
    rw [e] at hp ⊢
    obtain ⟨-, -, a3, a4⟩ := hnl hp
    have ha5 := (harr hp).1
    simp only [win, outside_cons, outside_nil, and_true, stW, stCap] at ha5
    rw [h0]
    refine ⟨a4, by rw [hF.accessible]; exact Memory.accessible_weaken _ a3, ?_⟩
    -- v0.3.1: the old array is outside the callee's window (it is outside the caller's window)
    simp only [stW, calleeStack, outside_cons, outside_nil, and_true]; omega

/-- the `memclrNoHeapPointers(p + 8·cap, 8·(len + nr - cap))` call after `growslice` returned the block `(p, 8·gc)` -/
theorem mcall_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st n : Nat} {s : State}
    (hpre : Pre R b L 4208 24 st n s) (hk : stCap s.mem st < stLen s.mem st + rnd n) {L1 : List (Nat × Nat)}
    {b1 p gc : Nat} (S : State)
    (hF : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)])) (hsp : S.sp.toNat + 112 = s.sp.toNat)
    (h28 : S.regs 28 = s.regs 28) (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hL1 : L1 = L ++ [(p, p + 8 * gc)]) (hgc : stLen s.mem st + rnd n ≤ gc)
    (hpin : InRanges p (8 * gc) R.rt) (hp48 : p + 8 * gc ≤ 2 ^ 48) (hpacc : S.mem.accessible p (8 * gc) true = true)
    (hinv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S.mem))
    (h0 : (S.regs 0).toNat = p + 8 * stCap s.mem st) (h1 : (S.regs 1).toNat = 8 * (stLen s.mem st + rnd n - stCap s.mem st)) :
    Mem.EqPre 4096 2 S ∧
      LiveMemAt R (cA "runtime.memclrNoHeapPointers") [(S.regs 0).toNat, (S.regs 1).toNat] L1 b1 S
        (calleeStack S 4096 2) ∧
      LiveDest R L1 S 4096 2 (S.regs 0).toNat (S.regs 1).toNat := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n ≤ n + 3 := by simp only [rnd]; omega
  unfold Apart at hga
  have hgo : Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4208, s.sp.toNat + 24) :: R.rt) := by
    simp only [outside_cons]; exact ⟨by omega, hgr⟩
  have hpw := hpin.apart hout
  unfold Apart at hpw
  have hLw : LiveSep L1 [(s.sp.toNat - 4208, s.sp.toNat + 24)] := by
    rw [hL1]; intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [outside_cons, outside_nil, and_true]; omega
  have hc := call_pre R L1 b1 0 (cA "runtime.memclrNoHeapPointers") [(S.regs 0).toNat, (S.regs 1).toNat]
    (s := s) (S := S) (lo := s.sp.toNat - 4208) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 2) (fr := 112)
    hg1 hg2 (by omega) hgo hF h28 hsp (by rw [← hsp] at hal; omega) h30a h30b (by decide) (by omega) (by omega)
    (by omega) ha (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4208) = 4208 + 24 by omega]; exact hw)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show s.sp.toNat + 24 - (s.sp.toNat - 4208) = 4208 + 24 by omega]; exact hout) hLw
    (hsv.2.2.1 _ _ (by rw [h1]; simp only [rnd] at hnr ⊢; omega)) (by rw [h28]; exact hinv) (Nat.zero_le _)
  obtain ⟨hco, ⟨hgk, hgout⟩, hok', hinv', -, hs1, hs2⟩ := hc
  refine ⟨⟨(guardOK_iff _ _).1 hgk, hco, hgout⟩, ⟨hok', hinv', hs1, hs2⟩, by omega, ?_, ?_, ?_⟩
  · rw [h0, h1]; exact Memory.accessible_mono _ hpacc (by omega) (by omega)
  · simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [h0, h1]; omega
  · left; rw [hL1, h0, h1]
    exact ⟨(p, p + 8 * gc), List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
      by simp only; omega⟩

end FvModexp.Arm64.StackNat
