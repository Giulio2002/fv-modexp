import FvModexp.Proofs.Arm64.Exp.ModInvOwn

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the round facts after a call (agent infra)

`after_zz` / `after_z`: the round facts `Mid` after a callee that writes `zz` (`sqr`, `trunc`, `mul`) / `z` (`lsh`,
`subMod2N`); the other array's words and the spill slots are unchanged. `nostk`: a callee whose frame does not
mention the stack object (`trunc`, `lsh`, `subMod2N`) leaves it alone.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- a callee whose frame misses the stack object leaves it alone -/
theorem nostk (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hS' : S'.sp.toNat = s.sp.toNat - 240)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)]))
    (hLF : LiveFrame M M' L1 [(t, t + 8 * tc)]) (hLE : LiveExt R L1 L2) :
    MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)] ++ stWs M st) ∧
      LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stWs M st) ∧ StackBack R L1 L2 st M M' ∧
      stW M' st = stW M st ∧ stCap M' st = stCap M st := by
  have hsp : 240 + kc ≤ s.sp.toNat := by
    have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have hstw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw
  have hok := hrt.2.2.2.2.2.1
  have hsh : Held R L1 st 24 := hok.2.1
  have ht8 := ht.2.2.2.2.2.2.2.1
  have hrd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := by
    intro j hj
    refine held_bytes (hsh.sub (by omega) (by omega)) hF hLF fun i hi => ⟨?_, ?_⟩
    · simp only [winA, hS', outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]
      rcases Nat.eq_zero_or_pos tc with h0 | h0
      · subst h0; omega
      · have := (ht8 (by omega)).1; unfold Apart at this; omega
  have e0 : stW M' st = stW M st := by have := hrd 0 (by omega); simpa only [Nat.add_zero] using this
  have e1 : stLen M' st = stLen M st := hrd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hrd 16 (by omega)
  exact ⟨hF.mono fun a k h => by simp only [outside_append] at h ⊢; exact h.1,
    FvModexp.LiveFrame.mono_ws hLF fun a k h => by simp only [outside_append] at h ⊢; exact h.1,
    stackBack_hdr hok hF e0 e1 e2 hLE, e0, e2⟩

set_option maxRecDepth 20000 in
/-- what a callee writing the owned array `t` leaves: runtime facts, spill slots, the other owned array `o` with its
words, and its result `t'` owned and apart from `o` -/
theorem after_core (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hkc : 4608 ≤ kc) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hS' : S'.sp.toNat = s.sp.toNat - 240) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc) (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(t, t + 8 * tc)] ++ stWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {o oc : Nat} (ho : Own R kc L L1 s zp zc st xp xl M o oc) (hoc : 0 < oc) (hot : Apart o (8 * oc) t (8 * tc))
    {t' tc' : Nat} (hlive : NatLive M' R L2 t' tc') (hc40 : tc' < 2 ^ 40) (hp : t' < 2 ^ 64)
    (hof : (t' = t ∧ tc' = tc) ∨ (InRanges t' (8 * tc') R.rt ∧ ApartAll t' (8 * tc') L1))
    (hstkA : ¬ (t' = t ∧ tc' = tc) → 0 < tc' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart t' (8 * tc') (stW M' st) (8 * stCap M' st)) :
    RtM R kc L s zp zc st M' L2 b2 ∧
      (∀ a, s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 152 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72 →
        M'.readLE a 8 = M.readLE a 8) ∧
      Own R kc L L2 s zp zc st xp xl M' o oc ∧ (∀ k, k ≤ oc → M'.readLE o (8 * k) = M.readLE o (8 * k)) ∧
      Own R kc L L2 s zp zc st xp xl M' t' tc' ∧ Apart o (8 * oc) t' (8 * tc') := by
  obtain ⟨h1, h2⟩ := keep_own hpre hrt hS' hstk habove hF hLF hLE hsb ho hot
  refine ⟨keep_rt hpre hrt hS' hkc hstk habove ht hreg hF hLF hLE hinv hsb hain,
    keep_slots hpre hrt hS' hkc hstk habove ht hF, h1, h2,
    own_new hpre hrt hsb ht hlive hc40 hp hof hstkA, ?_⟩
  rcases hof with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact hot
  · have := fresh_apart hIn hAp (ho.2.2.1 hoc).2.1
    unfold Apart at this ⊢; omega

theorem fw2_keep {M M' : Memory} (hs : ∀ a, s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232 ∨
      s.sp.toNat - 152 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72 → M'.readLE a 8 = M.readLE a 8)
    (hsp : 240 ≤ s.sp.toNat) (h : Fw2 s M st xp xl xc n) : Fw2 s M' st xp xl xc n := by
  obtain ⟨⟨f1, f2⟩, f3, f4, f5, f6, f7, f8, f9⟩ := h
  exact ⟨⟨(hs _ (by omega)).trans f1, (hs _ (by omega)).trans f2⟩, (hs _ (by omega)).trans f3,
    (hs _ (by omega)).trans f4, (hs _ (by omega)).trans f5, (hs _ (by omega)).trans f6, (hs _ (by omega)).trans f7,
    (hs _ (by omega)).trans f8, (hs _ (by omega)).trans f9⟩

set_option maxRecDepth 20000 in
/-- the round facts after a callee writing `zz` -/
theorem after_zz (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hkc : 4608 ≤ kc) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 p l c q ql qc : Nat}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hS' : S'.sp.toNat = s.sp.toNat - 240) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(q, q + 8 * qc)] ++ stWs M st))
    (hLF : LiveFrame M M' L1 ([(q, q + 8 * qc)] ++ stWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {q' ql' qc' : Nat} (hlive : NatLive M' R L2 q' qc') (hc40 : qc' < 2 ^ 40) (hq : q' < 2 ^ 64)
    (hof : (q' = q ∧ qc' = qc) ∨ (InRanges q' (8 * qc') R.rt ∧ ApartAll q' (8 * qc') L1))
    (hstkA : ¬ (q' = q ∧ qc' = qc) → 0 < qc' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart q' (8 * qc') (stW M' st) (8 * stCap M' st))
    (hql : ql' ≤ qc') (hqc : 0 < qc') :
    Mid R kc L s zp zc st xp xl xc n M' L2 b2 p l c q' ql' qc' ∧ natVal M' p l = natVal M p l ∧
      (∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 72 → M'.readLE a 8 = M.readLE a 8) := by
  obtain ⟨hfw, hrt, hz, hzz, hap, hlc, -, hnc, -⟩ := hmid
  have hsp : 240 ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simp only [K] at this; omega
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := after_core hpre hkc hrt hS' hstk habove hzz hreg hF hLF hLE hinv hsb hain hz
    (by omega) hap hlive hc40 hq hof hstkA
  exact ⟨⟨fw2_keep r2 hsp hfw, r1, r3, r5, r6, hlc, hql, hnc, hqc⟩, r4 l hlc,
    fun a h1 h2 => r2 a (Or.inr ⟨h1, h2⟩)⟩

set_option maxRecDepth 20000 in
/-- the round facts after a callee writing `z` -/
theorem after_z (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hkc : 4608 ≤ kc) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 p l c q ql qc : Nat}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hS' : S'.sp.toNat = s.sp.toNat - 240) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ winA S' stk above ++ [(p, p + 8 * c)] ++ stWs M st))
    (hLF : LiveFrame M M' L1 ([(p, p + 8 * c)] ++ stWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {p' l' c' : Nat} (hlive : NatLive M' R L2 p' c') (hc40 : c' < 2 ^ 40) (hp : p' < 2 ^ 64)
    (hof : (p' = p ∧ c' = c) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1))
    (hstkA : ¬ (p' = p ∧ c' = c) → 0 < c' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart p' (8 * c') (stW M' st) (8 * stCap M' st))
    (hl : l' ≤ c') (hc : NW n + 1 ≤ c') :
    Mid R kc L s zp zc st xp xl xc n M' L2 b2 p' l' c' q ql qc ∧
      (∀ k, k ≤ qc → M'.readLE q (8 * k) = M.readLE q (8 * k)) ∧
      (∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 72 → M'.readLE a 8 = M.readLE a 8) := by
  obtain ⟨hfw, hrt, hz, hzz, hap, -, hqlc, hnc, hqc⟩ := hmid
  have hsp : 240 ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have hap' : Apart q (8 * qc) p (8 * c) := by unfold Apart at hap ⊢; omega
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := after_core hpre hkc hrt hS' hstk habove hz hreg hF hLF hLE hinv hsb hain hzz
    hqc hap' hlive hc40 hp hof hstkA
  exact ⟨⟨fw2_keep r2 hsp hfw, r1, r5, r3, by unfold Apart at r6 ⊢; omega, hl, hqlc, hc, hqc⟩, r4,
    fun a h1 h2 => r2 a (Or.inr ⟨h1, h2⟩)⟩

end

end FvModexp.Arm64.ModInv
