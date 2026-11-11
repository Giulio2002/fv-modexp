import FvModexp.Proofs.Arm64.Exp.ModInvRnd

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): what survives a callee that writes one owned array (agent infra)

A callee at `SP' = SP - 240` (window `stk ≤ kc`, `above ≤ 88`) whose frame is `R.rt ++ winA SP' ++ [t] ++ stWs M st`
(`t` an owned array) keeps: the runtime facts (`RtM`), the spill slots, every other owned array apart from `t` (with
its words), `x`'s words (`call_keep`); its result is owned (`own_new`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

theorem out_sub {p n a k i j : Nat} {rs : List (Nat × Nat)} (hin : InRanges p n rs) (ho : Outside a k rs)
    (_hij : i ≤ j) (hj : j ≤ n) : Outside a k [(p + i, p + j)] := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem ho hr
  simp only [outside_cons, outside_nil, and_true]; omega

/-- an owned array stays owned after a callee: its array is live in the new live set, and the stack came back -/
theorem own_back {R : RtInv} {kc : Nat} {L L1 L2 : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat}
    {M M' : Memory} {o oc : Nat} (h : Own R kc L L1 s zp zc st xp xl M o oc) (hlive : NatLive M' R L2 o oc)
    (hsb : StackBack R L1 L2 st M M') : Own R kc L L2 s zp zc st xp xl M' o oc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨a1, a2, hlive, a4, a5, a6, a7, fun hc => ?_⟩
  have hc' : 0 < oc := by omega
  exact stkApart_back hsb a8 (a3 hc').2.1 hc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- what a callee that writes the owned array `t` keeps (see the module doc) -/
theorem call_keep {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 b2 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hS' : S'.sp.toNat = s.sp.toNat - 240)
    {stk above : Nat} (hkc : 4608 ≤ kc) (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc) (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)] ++ stWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M') :
    RtM R kc L s zp zc st M' L2 b2 ∧
      (∀ a, (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 152 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72) →
        M'.readLE a 8 = M.readLE a 8) ∧
      (∀ o oc, Own R kc L L1 s zp zc st xp xl M o oc → Apart o (8 * oc) t (8 * tc) →
        Own R kc L L2 s zp zc st xp xl M' o oc ∧ ∀ k, k ≤ oc → M'.readLE o (8 * k) = M.readLE o (8 * k)) := by
  obtain ⟨⟨-, ⟨-, hb', -, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, hstw, -, hsta⟩, -, -, -, -, -, -, -, -⟩ := hpre
  have hrt' := hrt
  obtain ⟨-, -, -, LE0, -, hstk0, len0, arr0⟩ := hrt'
  obtain ⟨-, -, -, t4, t5, -, -, -⟩ := ht
  have hlc : stLen M st ≤ stCap M st := hstk0.2.2.2.2.2.1
  simp only [K, A] at hout hb' hLs hstw t5 hsta
  simp only [win, outside_cons, outside_nil, and_true] at hstw t5 hsta
  have hS2 := hS'
  -- the stack's free part at `M`, per byte inside the window and per range outside the runtime ranges
  have hfp : ∀ a, s.sp.toNat - (240 + kc) ≤ a → a + 1 ≤ s.sp.toNat + 72 →
      Outside a 1 [(stW M st + 8 * stLen M st, stW M st + 8 * stCap M st)] := by
    intro a h1 h2
    rcases arr0 with ⟨e0, e2⟩ | ⟨hIn, -⟩
    · rw [e0, e2, len0]
      simp only [outside_cons, outside_nil, and_true]
      rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
      · rw [e2, h0] at hlc; rw [h0]; omega
      · have := (hsta h0).1; omega
    · exact out_sub hIn (hout.of_sub (by omega) (by omega)) (Nat.mul_le_mul_left 8 hlc) (Nat.le_refl _)
  refine ⟨rtM_call hrt hreg (ws := winA S' stk above ++ ([(t, t + 8 * tc)] ++ stWs M st))
    (by simpa only [List.append_assoc] using hF) ?_
    ⟨fun a k h ho => hLF.readLE a k h (by simp only [outside_append] at ho ⊢; exact ho.2)⟩ ?_ hLE hinv hsb, ?_, ?_⟩
  · -- `hws`
    intro a k h
    simp only [outside_append] at h ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, ?_, ?_, ?_⟩
    · simp only [winA, K, A, hS', outside_cons, outside_nil, and_true] at h2 ⊢; omega
    · rcases t4 with ⟨rfl, rfl⟩ | ⟨hIn, -⟩
      · exact h3
      · simpa using out_sub hIn h1 (Nat.zero_le _) (Nat.le_refl _)
    · simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at h4 ⊢
      refine ⟨h4.1, ?_⟩
      rcases arr0 with ⟨e0, e2⟩ | ⟨hIn, -⟩
      · rw [e0, e2, len0]; exact h4.2
      · have := out_sub hIn h1 (Nat.mul_le_mul_left 8 hlc) (Nat.le_refl _)
        simp only [outside_cons, outside_nil, and_true] at this; exact this
  · -- `hwsL`
    intro a k hin h
    obtain ⟨r, hr, hr1, hr2⟩ := hin
    have hrw := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at hrw
    simp only [outside_append] at h ⊢
    obtain ⟨h3, h4⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · simp only [winA, hS', outside_cons, outside_nil, and_true]; omega
    · rcases t4 with ⟨rfl, rfl⟩ | ⟨-, hAp⟩
      · exact h3
      · have := hAp r hr; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [stWs, stkWs, outside_cons, outside_nil, and_true] at h4 ⊢
      refine ⟨h4.1, ?_⟩
      rcases arr0 with ⟨e0, e2⟩ | ⟨-, hAp⟩
      · rw [e0, e2, len0]; exact h4.2
      · have := hAp r hr; unfold Apart at this; omega
  · -- the spill slots
    intro a ha
    refine frame_bytes hF fun i hi => ?_
    simp only [outside_append]
    refine ⟨⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
    · simp only [winA, hS', outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [stWs, stkWs, outside_cons, outside_nil, and_true]
      have := hfp (a + i) (by omega) (by omega)
      simp only [outside_cons, outside_nil, and_true] at this
      exact ⟨by omega, this⟩
  · -- a kept owned array
    intro o oc ho hot
    have ho' := ho
    obtain ⟨-, -, o3, -, o5, -, -, o8⟩ := ho'
    simp only [win, K, A, outside_cons, outside_nil, and_true] at o5
    unfold Apart at hot
    have hlive : NatLive M' R L2 o oc := fun hc => by
      obtain ⟨c1, c2, c3, c4⟩ := o3 hc
      exact ⟨c1, hLE.held c2, by rw [hF.accessible]; exact c3, c4⟩
    refine ⟨own_back ho hlive hsb, fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos oc with h0 | h0
    · have : k = 0 := by omega
      subst this; rfl
    obtain ⟨-, hh, -, -⟩ := o3 h0
    obtain ⟨s1, s2⟩ := o8 (by omega)
    unfold Apart at s1
    rw [List.append_assoc] at hF
    refine held_bytes (hh.sub (Nat.le_refl _) (by omega)) hF hLF fun i hi => ⟨?_, ?_⟩
    · simp only [winA, hS', outside_cons, outside_nil, and_true]; omega
    · simp only [stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]
      refine ⟨by omega, by omega, ?_⟩
      rcases Nat.lt_or_ge (stLen M st) (stCap M st) with h | h
      · have := s2 h; unfold Apart at this; omega
      · omega

end FvModexp.Arm64.ModInv
