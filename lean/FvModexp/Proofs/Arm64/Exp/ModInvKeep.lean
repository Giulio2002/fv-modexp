import FvModexp.Proofs.Arm64.Exp.ModInvRnd

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the runtime facts survive a callee that writes one owned array (agent infra)

A callee at `SP' = SP - 240` (window `stk ≤ kc`, `above ≤ 88`) whose frame is `R.rt ++ winA SP' ++ [t] ++ stWs M st`
(`t` an owned array) keeps the runtime facts `RtM` (`keep_rt`). The spill slots and the other owned arrays:
`ModInvKeep2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

/-- the callee's writable ranges are inside the function's (arithmetic core of `keep_rt`) -/
theorem keep_ws {rt : List (Nat × Nat)} {sp kc stk above sp' t tc zp zc w0 l0 c0 w l c st : Nat}
    (hS' : sp' = sp - 240) (hkc : 4608 ≤ kc) (hstk : stk ≤ kc) (habove : above ≤ 88) (hsp : 240 + kc ≤ sp)
    (ht : (t = zp ∧ tc = zc) ∨ InRanges t (8 * tc) rt) (hlc : l ≤ c)
    (hst : (w = w0 ∧ c = c0 ∧ l = l0) ∨ InRanges w (8 * c) rt) {a k : Nat}
    (h : Outside a k (rt ++ [(sp - (240 + kc), sp - 8), (sp + 8, sp + 72)] ++ [(zp, zp + 8 * zc)] ++
      [(st, st + 24), (w0 + 8 * l0, w0 + 8 * c0)])) :
    Outside a k (rt ++ ([(sp' - stk, sp' - 8), (sp' + 8, sp' + above)] ++ ([(t, t + 8 * tc)] ++
      [(st, st + 24), (w + 8 * l, w + 8 * c)]))) := by
  simp only [outside_append] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · simp only [outside_cons, outside_nil, and_true] at h2 ⊢; omega
  · rcases ht with ⟨rfl, rfl⟩ | hIn
    · exact h3
    · simpa using out_sub hIn h1 (Nat.zero_le _) (Nat.le_refl _)
  · simp only [outside_cons, outside_nil, and_true] at h4 ⊢
    refine ⟨h4.1, ?_⟩
    rcases hst with ⟨rfl, rfl, rfl⟩ | hIn
    · exact h4.2
    · have := out_sub hIn h1 (Nat.mul_le_mul_left 8 hlc) (Nat.le_refl _)
      simp only [outside_cons, outside_nil, and_true] at this; exact this

/-- the callee's writable ranges miss the entry's live ranges outside the function's writes -/
theorem keep_wsL {L : List (Nat × Nat)} {sp kc stk above sp' t tc zp zc w0 l0 c0 w l c st : Nat}
    (hS' : sp' = sp - 240) (hstk : stk ≤ kc) (habove : above ≤ 88) (hsp : 240 + kc ≤ sp)
    (hLs : ∀ r ∈ L, Outside r.1 (r.2 - r.1) [(sp - (240 + kc), sp + 72)])
    (ht : (t = zp ∧ tc = zc) ∨ ApartAll t (8 * tc) L)
    (hst : (w = w0 ∧ c = c0 ∧ l = l0) ∨ ApartAll w (8 * c) L) (hlc : l ≤ c) {a k : Nat} (hin : InRanges a k L)
    (h : Outside a k ([(zp, zp + 8 * zc)] ++ [(st, st + 24), (w0 + 8 * l0, w0 + 8 * c0)])) :
    Outside a k ([(sp' - stk, sp' - 8), (sp' + 8, sp' + above)] ++ ([(t, t + 8 * tc)] ++
      [(st, st + 24), (w + 8 * l, w + 8 * c)])) := by
  obtain ⟨r, hr, hr1, hr2⟩ := hin
  have hrw := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at hrw
  simp only [outside_append] at h ⊢
  obtain ⟨h3, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · rcases ht with ⟨rfl, rfl⟩ | hAp
    · exact h3
    · have := hAp r hr; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true] at h4 ⊢
    refine ⟨h4.1, ?_⟩
    rcases hst with ⟨rfl, rfl, rfl⟩ | hAp
    · exact h4.2
    · have := hAp r hr; unfold Apart at this; omega

set_option maxRecDepth 20000 in
/-- the runtime facts survive a callee that writes the owned array `t` -/
theorem keep_rt {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 b2 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hS' : S'.sp.toNat = s.sp.toNat - 240)
    {stk above : Nat} (hkc : 4608 ≤ kc) (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc) (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)] ++ stWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M') : RtM R kc L s zp zc st M' L2 b2 := by
  have hsp : 240 + kc ≤ s.sp.toNat := by
    have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have hLs := hpre.1.2.2.2.2.2.2.1
  simp only [win, K, A] at hLs
  have hrt' := hrt
  obtain ⟨-, -, -, LE0, -, hstk0, len0, arr0, -⟩ := hrt'
  have hlc : stLen M st ≤ stCap M st := hstk0.2.2.2.2.2.1
  have t4 := ht.2.2.2.1
  refine rtM_call hrt hreg (ws := winA S' stk above ++ ([(t, t + 8 * tc)] ++ stWs M st))
    (by simpa only [List.append_assoc] using hF) (fun a k h => ?_)
    ⟨fun a k h ho => hLF.readLE a k h (by simp only [outside_append] at ho ⊢; exact ho.2)⟩ (fun a k hin h => ?_)
    hLE hinv hsb hain
  · simp only [winA, stWs, stkWs, hS', K, A] at h ⊢
    exact keep_ws rfl hkc hstk habove hsp (t4.imp id fun h => h.1) hlc
      (arr0.imp (fun ⟨e0, e2⟩ => ⟨e0, e2, len0⟩) fun h => h.1) h
  · simp only [winA, stWs, stkWs, hS'] at h ⊢
    exact keep_wsL rfl hstk habove hsp hLs (t4.imp id fun h => h.2)
      (arr0.imp (fun ⟨e0, e2⟩ => ⟨e0, e2, len0⟩) fun h => h.2) hlc hin h

end FvModexp.Arm64.ModInv
