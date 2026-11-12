import FvModexp.Proofs.Arm64.Exp.ModInvRnd

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the spill slots and the other owned arrays survive a callee (agent infra)

A callee at `SP' = SP - 240` (window `stk ≤ kc`, `above ≤ 88`) whose frame is `R.rt ++ winA SP' ++ [t] ++ stWs M st`
(`t` an owned array) keeps the spill slots `[SP - 248, SP - 232) ∪ [SP - 152, SP + 72)` (`keep_slots`) and every
owned array apart from `t`, with its words (`keep_own`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

set_option maxRecDepth 20000 in
/-- the stack's free part at `M` misses the function's window -/
theorem keep_fp {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) (a : Nat) (h1 : s.sp.toNat - (240 + kc) ≤ a)
    (h2 : a + 1 ≤ s.sp.toNat + 72) : Outside a 1 [(stW M st + 8 * stLen M st, stW M st + 8 * stCap M st)] := by
  have hout := hpre.1.2.2.2.1
  have hsta := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨-, -, -, -, -, hstk0, len0, arr0, -⟩ := hrt
  have hlc : stLen M st ≤ stCap M st := hstk0.2.2.2.2.2.1
  simp only [K, A] at hout
  rcases arr0 with ⟨e0, e2⟩ | ⟨hIn, -⟩
  · rw [e0, e2, len0]
    simp only [outside_cons, outside_nil, and_true]
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · rw [e2, h0] at hlc; rw [h0]; omega
    · have := (hsta h0).1
      simp only [win, K, A, outside_cons, outside_nil, and_true] at this; omega
  · exact out_sub hIn (hout.of_sub (by omega) (by omega)) (Nat.mul_le_mul_left 8 hlc) (Nat.le_refl _)

set_option maxRecDepth 20000 in
/-- the spill slots survive a callee -/
theorem keep_slots {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hS' : S'.sp.toNat = s.sp.toNat - 240)
    {stk above : Nat} (hkc : 4608 ≤ kc) (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)] ++ stWs M st)) (a : Nat)
    (ha : s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 152 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72) :
    M'.readLE a 8 = M.readLE a 8 := by
  have hsp : 240 + kc ≤ s.sp.toNat := by
    have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have hout := hpre.1.2.2.2.1
  have hstw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have t5 := ht.2.2.2.2.1
  simp only [K, A] at hout
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw t5
  refine frame_bytes hF fun i hi => ?_
  have hfp := keep_fp hpre hrt (a + i) (by omega) (by omega)
  simp only [outside_cons, outside_nil, and_true] at hfp
  simp only [outside_append]
  refine ⟨⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [winA, hS', outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stWs, stkWs, outside_cons, outside_nil, and_true]
    exact ⟨by omega, hfp⟩

set_option maxRecDepth 20000 in
/-- an owned array apart from `t` survives a callee, with its words -/
theorem keep_own {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hS' : S'.sp.toNat = s.sp.toNat - 240)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)] ++ stWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stWs M st)) (hLE : LiveExt R L1 L2)
    (hsb : StackBack R L1 L2 st M M') {o oc : Nat} (ho : Own R kc L L1 s zp zc st xp xl M o oc)
    (hot : Apart o (8 * oc) t (8 * tc)) :
    Own R kc L L2 s zp zc st xp xl M' o oc ∧ ∀ k, k ≤ oc → M'.readLE o (8 * k) = M.readLE o (8 * k) := by
  have hlc : stLen M st ≤ stCap M st := hrt.2.2.2.2.2.1.2.2.2.2.2.1
  have hsp : 240 + kc ≤ s.sp.toNat := by
    have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have ho' := ho
  obtain ⟨-, -, o3, -, o5, -, -, o8, -⟩ := ho'
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
