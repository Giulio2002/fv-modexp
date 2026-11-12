import FvModexp.Proofs.Arm64.Exp.OddDefs

/-!
# `nat.expNNOdd` (arm64): the postcondition from a window's postcondition

A window's post (`ExpW4.PostD` / `ExpW2.PostD`, unfolded: cost `C`, stack window `stk`) at its entry state `S` (after
the prologue's stores, frame of the stores `[(sp + 920, sp + 936), (sp + 1064, sp + 1152)]`) and the epilogue's final
state `s''` give `ExpOdd.Post` at the entry state `s`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpOdd

theorem ap_sub1 {a k lo n a' k' : Nat} (h : Apart a k lo n) (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) :
    Apart a' k' lo n := by
  unfold Apart at h ⊢; omega

theorem out_win {a k sp K : Nat} (h : Apart a k (sp - K) (K + 1168)) (hK : K ≤ sp) :
    Outside a k [(sp + 920, sp + 936), (sp + 1064, sp + 1152)] := by
  unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- `expNNOdd`'s saved FP / LR slots (`sp + 920`, `sp + 928`) are outside a window's written ranges -/
theorem slot_keep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat}
    {g sp st zp zc xp xl xc yp ylen mp n mc : Nat} {s S : State} {stk j : Nat}
    (hP : OPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s)
    (hFs : MemFrame s.mem S.mem [(sp + 920, sp + 936), (sp + 1064, sp + 1152)])
    (hSsp : S.sp.toNat = sp + 928) (hstk : stk ≤ K + 928) (hj : j = 920 ∨ j = 928) :
    Outside (sp + j) 8 (R.rt ++ winA S stk 112 ++ [(zp, zp + 8 * zc)] ++ stkWs S.mem st) := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, hK', -, -, hwrt, -, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzW, -, -, -, hstw, -, harr, hc0, -⟩ := hP
  have rd : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1168) → S.mem.readLE a k = s.mem.readLE a k :=
    fun h => hFs.readLE _ _ (out_win h hK')
  have ew : stW S.mem st = stW s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
  have el : stLen S.mem st = stLen s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
  have ec : stCap S.mem st = stCap s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
  have hrt : Outside (sp - K) (K + 1168) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    exact Outside.of_sub this (by simp only; omega) (by simp only; omega)
  have hfree : sp + j + 8 ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ sp + j := by
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · have := hc0 h0; omega
    · have := (harr h0).1; unfold Apart at this; omega
  unfold Apart at hzW hstw
  rw [outside_append, outside_append, outside_append]
  refine ⟨⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [winA, hSsp, outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, ew, el, ec, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem post_gen {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {g sp st zp zc xp xl xc yp ylen mp n mc : Nat} {s S s' s'' : State} {C stk : Nat}
    (hP : OPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s)
    (hFs : MemFrame s.mem S.mem [(sp + 920, sp + 936), (sp + 1064, sp + 1152)])
    (hSsp : S.sp.toNat = sp + 928) (hstk : stk ≤ K + 928) (h28 : S.regs 28 = s.regs 28)
    (hC : C = OCost costF n xl ylen (stLen s.mem st) ∨ C = OCost costF n xl ylen (stLen S.mem st))
    (hq : ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧
      s'.regs 2 = BitVec.ofNat 64 c ∧
      natVal s'.mem p l = natVal S.mem xp xl ^ natVal S.mem yp ylen % natVal S.mem mp n ∧ NatNorm s'.mem p l ∧
      l ≤ c ∧ c < 2 ^ 64 ∧
      ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - C ≤ b' ∧
        R.inv b' L' (S.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
        ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
        StackBack R L L' st S.mem s'.mem ∧
        MemFrame S.mem s'.mem (R.rt ++ winA S stk 112 ++ [(zp, zp + 8 * zc)] ++ stkWs S.mem st) ∧
        LiveFrame S.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs S.mem st))
    (e0 : s''.regs 0 = s'.regs 0) (e1 : s''.regs 1 = s'.regs 1) (e2 : s''.regs 2 = s'.regs 2)
    (em : s''.mem = s'.mem) :
    Post R b L K costF zp zc st xp xl yp ylen mp n s s'' := by
  obtain ⟨⟨hs1, hs28, -, -, -, -, -, -, hK', hsp2, -, hwrt, hLs, -, -⟩, -, -, -, -, -, -, -, -, hmO, -, -, -, hyO,
    -, -, -, -, -, hxO, -, -, -, -, -, -, -, -, -, hzW, -, -, -, hstw, -, harr, hc0, -, -, -, -, -⟩ := hP
  have hssp : s.sp.toNat = sp + 1056 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have rd : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1168) → S.mem.readLE a k = s.mem.readLE a k :=
    fun h => hFs.readLE _ _ (out_win h hK')
  have ew : stW S.mem st = stW s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
  have el : stLen S.mem st = stLen s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
  have ec : stCap S.mem st = stCap s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
  have hws : stkWs S.mem st = stkWs s.mem st := by simp only [stkWs, ew, el, ec]
  obtain ⟨p, l, c, q0, q1, q2, hv, hn, hlc, hc, L', b', hx, hb, hinv, hlive, hof, hsb, hF, hLF⟩ := hq
  have hrt : Outside (sp - K) (K + 1168) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    exact Outside.of_sub this (by simp only; omega) (by simp only; omega)
  refine ⟨p, l, c, e0.trans q0, e1.trans q1, e2.trans q2, ?_, by rw [em]; exact hn, hlc, hc, L', b', hx, ?_,
    by rw [em, ← h28]; exact hinv, by rw [em]; exact hlive, hof, ?_, ?_, ?_⟩
  · rw [em, hv]; simp only [natVal]; rw [rd hxO.2.1, rd hyO.2.1, rd hmO.2.1]
  · rcases hC with rfl | rfl
    · exact hb
    · rw [el] at hb; exact hb
  · obtain ⟨k1, k2, k3⟩ := hsb
    rw [em]; exact ⟨k1, k2.trans el, by rw [← ew, ← ec]; exact k3⟩
  · rw [em]
    refine MemFrame.trans hFs hF fun a k ho => ?_
    rw [outside_append, outside_append, outside_append] at ho
    obtain ⟨⟨⟨hr, hw⟩, hz⟩, hs⟩ := ho
    simp only [winA, hssp, outside_cons, outside_nil, and_true] at hw
    refine ⟨by simp only [outside_cons, outside_nil, and_true]; omega, ?_⟩
    rw [hws, outside_append, outside_append, outside_append]
    refine ⟨⟨⟨hr, ?_⟩, hz⟩, hs⟩
    simp only [winA, hSsp, outside_cons, outside_nil, and_true]; omega
  · rw [em, ← hws]
    refine (LiveFrame.of_win (hFs.mono fun a k ho => ?_) (LiveSep.sub_win hLs (Nat.le_refl (sp - K))
      (show sp + 1168 ≤ sp + 1168 from Nat.le_refl _))).trans hLF fun _ _ h => h
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega

end FvModexp.Arm64.ExpOdd
