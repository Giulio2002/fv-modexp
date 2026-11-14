import FvModexp.Proofs.Amd64.Exp.ModInvRnd
import FvModexp.Proofs.Amd64.Exp.ModInvSt

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the round facts after a callee (agent infra s57; twin of
`Arm64/Exp/ModInvAfter` / `ModInvOwn` / `ModInvKeep2`)

A callee entered at `RSP_c = RSP - 232` (window `[RSP_c - stk, RSP_c + above)`, `stk ≤ kc`, `above ≤ 88`) writing the
owned array `t` (frame `R.rt ++ win ++ [t] ++ stkWs M st`): `keep_slots` (every slot at or above `RSP - 144`),
`keep_own` (another owned array, with its words), `own_new` (the callee's result is owned), `after_core`,
`after_zz` / `after_z` (the round facts `Mid` with the new `zz` / `z`), `nostk` (a callee without stack object:
lift its frame). Pure lemmas.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

theorem apart_free' {p n w c l : Nat} (h : Apart p n w (8 * c)) (hlc : l ≤ c) : Apart p n (w + 8 * l) (8 * (c - l)) := by
  unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
/-- the stack's free part at `M` misses the function's window -/
theorem keep_fp (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) (a : Nat) (h1 : (s.regs 4).toNat - (232 + kc) ≤ a)
    (h2 : a + 1 ≤ (s.regs 4).toNat + 72) :
    Outside a 1 [(stW M st + 8 * stLen M st, stW M st + 8 * stCap M st)] := by
  obtain ⟨⟨-, -, -, -, hout, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, hsta, -⟩, -⟩ := hpre
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
/-- the slots at or above `RSP - 144` survive a callee -/
theorem keep_slots (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    {t tc : Nat} (ht : Own R kc L L1 s zp zc st xp xl M t tc)
    (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(t, t + 8 * tc)] ++ stkWs M st)) (a : Nat)
    (ha1 : (s.regs 4).toNat - 144 ≤ a) (ha2 : a + 8 ≤ (s.regs 4).toNat + 72) :
    M'.readLE a 8 = M.readLE a 8 := by
  have hsp := sp_K hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hpre'
  have t5 := ht.2.2.2.2.1
  simp only [K, A] at hout
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw t5
  refine frame_bytes hF fun i hi => ?_
  have hfp := keep_fp hpre hrt (a + i) (by omega) (by omega)
  simp only [outside_cons, outside_nil, and_true] at hfp
  simp only [outside_append]
  refine ⟨⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [win, hS', outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, outside_cons, outside_nil, and_true]
    exact ⟨by omega, hfp⟩

set_option maxRecDepth 20000 in
/-- an owned array apart from `t` survives a callee, with its words -/
theorem keep_own (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    {t tc : Nat} (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(t, t + 8 * tc)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stkWs M st)) (hLE : LiveExt R L1 L2)
    (hsb : StackBack R L1 L2 st M M') {o oc : Nat} (ho : Own R kc L L1 s zp zc st xp xl M o oc) (hoc : 0 < oc)
    (hot : Apart o (8 * oc) t (8 * tc)) :
    Own R kc L L2 s zp zc st xp xl M' o oc ∧ ∀ k, k ≤ oc → M'.readLE o (8 * k) = M.readLE o (8 * k) := by
  have hsp := sp_K hpre
  have ho' := ho
  obtain ⟨-, -, o3, -, o5, -, -, -, o9, -⟩ := ho'
  simp only [win, K, A, outside_cons, outside_nil, and_true] at o5
  unfold Apart at hot
  have hlive : NatLive M' R L2 o oc := fun hc => by
    obtain ⟨c1, c2, c3, c4⟩ := o3 hc
    exact ⟨c1, hLE.held c2, by rw [hF.accessible]; exact c3, c4⟩
  refine ⟨own_back ho hoc hlive hsb, fun k hk => ?_⟩
  obtain ⟨-, hh, -, -⟩ := o3 hoc
  obtain ⟨s1, s2, -⟩ := o9
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at s2
  unfold Apart at s1 s2
  rw [List.append_assoc] at hF
  refine held_bytes (hh.sub (Nat.le_refl _) (by omega)) hF hLF fun i hi => ⟨?_, ?_⟩
  · simp only [win, hS', outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨by omega, by omega, by omega⟩

set_option maxRecDepth 20000 in
/-- the stack's free part at a memory the runtime facts describe is held by the current live set -/
theorem free_held (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) :
    Held R L1 (Q.BasicSqr.freeP M st) (Q.BasicSqr.freeN M st) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, hfh, -⟩, -⟩ := hpre
  obtain ⟨-, -, -, hLE, -, hok, hlen, -, hain⟩ := hrt
  have hlc : stLen M st ≤ stCap M st := hok.2.2.2.2.2.1
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hfh ⊢
  by_cases hold : stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  · obtain ⟨e0, e2⟩ := hold
    rw [e0, e2, hlen]; exact hLE.held hfh
  · obtain ⟨hmem, -⟩ := hain hold
    exact Or.inl ⟨_, hmem, by omega, by omega⟩

set_option maxRecDepth 20000 in
/-- the result array of a callee is owned -/
theorem own_new (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {t tc p' c' : Nat} (ht : Own R kc L L1 s zp zc st xp xl M t tc) (htc : 0 < tc) (hlive : NatLive M' R L2 p' c')
    (hc0 : 0 < c') (hc40 : c' < 2 ^ 40) (hp : p' < 2 ^ 64)
    (hof : (p' = t ∧ c' = tc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1))
    (hstk : ¬ (p' = t ∧ c' = tc) → 0 < c' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart p' (8 * c') (stW M' st) (8 * stCap M' st)) :
    Own R kc L L2 s zp zc st xp xl M' p' c' := by
  rcases hof with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact own_back ht htc hlive hsb
  by_cases hold : p' = t ∧ c' = tc
  · obtain ⟨rfl, rfl⟩ := hold; exact own_back ht htc hlive hsb
  have hwa := wa_new hsb hrt.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2.2 (fun hc => (ht.2.2.1 hc).2.1) (Or.inr ⟨hIn, hAp⟩) hstk
  have hfh := free_held hpre hrt
  obtain ⟨⟨-, -, -, -, hout, -, hgrt, -, -, ⟨-, htrt, -⟩⟩, -, ⟨⟨-, -, -, -, -, -, -, -, hgArt, -⟩, -⟩, -, -, -, -, -, -,
    -, -, -, -, ⟨-, -, -, hxh, -⟩, -⟩ := hpre
  obtain ⟨-, -, -, LE0, -, ⟨-, hsth, -, -, -, -, -⟩, -, -⟩ := hrt
  have hApL : ApartAll p' (8 * c') L := apartAll_old LE0 hAp
  simp only [K, A] at hout
  refine ⟨hc40, hp, hlive, Or.inr ⟨hIn, hApL⟩, ?_, fresh_out hIn hgrt, fresh_out hIn htrt,
    fresh_apart hIn hApL (hxh.sub (Nat.le_refl _) (by omega)), ⟨(fresh_apart hIn hAp hsth).symm, ?_, fresh_out hIn hgArt⟩, hwa⟩
  · have := fresh_out hIn hout
    unfold Apart at this
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  · obtain ⟨hok, hlen, -⟩ := hsb
    have hlc' : stLen M' st ≤ stCap M' st := hok.2.2.2.2.2.1
    by_cases hsame : stW M' st = stW M st ∧ stCap M' st = stCap M st
    · obtain ⟨e0, e2⟩ := hsame
      simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hfh ⊢
      rw [e0, e2, hlen]
      exact fresh_apart hIn hAp hfh
    · have hk0 := (hain hsame).2
      have hfull := hstk hold hc0 hk0 hsame
      simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]
      exact apart_free' hfull hlc'

set_option maxRecDepth 20000 in
/-- what a callee writing the owned array `t` leaves: runtime facts, the slots, the other owned array `o` with its
words, and its result `t'` owned and apart from `o` -/
theorem after_core (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    {t tc : Nat} (ht : Own R kc L L1 s zp zc st xp xl M t tc) (htc : 0 < tc) (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(t, t + 8 * tc)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stkWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {o oc : Nat} (ho : Own R kc L L1 s zp zc st xp xl M o oc) (hoc : 0 < oc) (hot : Apart o (8 * oc) t (8 * tc))
    {t' tc' : Nat} (hlive : NatLive M' R L2 t' tc') (htc' : 0 < tc') (hc40 : tc' < 2 ^ 40) (hp : t' < 2 ^ 64)
    (hof : (t' = t ∧ tc' = tc) ∨ (InRanges t' (8 * tc') R.rt ∧ ApartAll t' (8 * tc') L1))
    (hstkA : ¬ (t' = t ∧ tc' = tc) → 0 < tc' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart t' (8 * tc') (stW M' st) (8 * stCap M' st)) :
    RtM R kc L s zp zc st M' L2 b2 ∧
      (∀ a, (s.regs 4).toNat - 144 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 → M'.readLE a 8 = M.readLE a 8) ∧
      Own R kc L L2 s zp zc st xp xl M' o oc ∧ (∀ k, k ≤ oc → M'.readLE o (8 * k) = M.readLE o (8 * k)) ∧
      Own R kc L L2 s zp zc st xp xl M' t' tc' ∧ Apart o (8 * oc) t' (8 * tc') := by
  obtain ⟨h1, h2⟩ := keep_own hpre hrt hS' hstk habove hF hLF hLE hsb ho hoc hot
  refine ⟨keep_rt hpre hrt hS' hstk habove ht hreg hF hLF hLE hinv hsb hain,
    fun a h1 h2 => keep_slots hpre hrt hS' hstk habove ht hF a h1 h2, h1, h2,
    own_new hpre hrt hsb hain ht htc hlive htc' hc40 hp hof hstkA, ?_⟩
  rcases hof with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact hot
  · have := fresh_apart hIn hAp (ho.2.2.1 hoc).2.1
    unfold Apart at this ⊢; omega

theorem fw2_keep {M M' : Memory} (hs : ∀ a, (s.regs 4).toNat - 144 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 →
      M'.readLE a 8 = M.readLE a 8) (hsp : 232 ≤ (s.regs 4).toNat) (h : Fw2 s M st xp xl xc n) :
    Fw2 s M' st xp xl xc n := by
  obtain ⟨⟨f1, f2⟩, f3, f4, f5, f6, f7, f9⟩ := h
  exact ⟨⟨(hs _ (by omega) (by omega)).trans f1, (hs _ (by omega) (by omega)).trans f2⟩,
    (hs _ (by omega) (by omega)).trans f3, (hs _ (by omega) (by omega)).trans f4, (hs _ (by omega) (by omega)).trans f5,
    (hs _ (by omega) (by omega)).trans f6, (hs _ (by omega) (by omega)).trans f7, (hs _ (by omega) (by omega)).trans f9⟩

set_option maxRecDepth 20000 in
/-- the round facts after a callee writing `zz` -/
theorem after_zz (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 p l c q ql qc : Nat}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(q, q + 8 * qc)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(q, q + 8 * qc)] ++ stkWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {q' ql' qc' : Nat} (hlive : NatLive M' R L2 q' qc') (hc40 : qc' < 2 ^ 40) (hq : q' < 2 ^ 64)
    (hof : (q' = q ∧ qc' = qc) ∨ (InRanges q' (8 * qc') R.rt ∧ ApartAll q' (8 * qc') L1))
    (hstkA : ¬ (q' = q ∧ qc' = qc) → 0 < qc' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart q' (8 * qc') (stW M' st) (8 * stCap M' st))
    (hql : ql' ≤ qc') (hqc : 0 < qc') :
    Mid R kc L s zp zc st xp xl xc n M' L2 b2 p l c q' ql' qc' ∧ natVal M' p l = natVal M p l ∧
      (∀ a, (s.regs 4).toNat - 144 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 → M'.readLE a 8 = M.readLE a 8) := by
  obtain ⟨hfw, hrt, hz, hzz, hap, hlc, -, hnc, hqc0⟩ := hmid
  have hsp := sp_K hpre
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := after_core hpre hrt hS' hstk habove hzz hqc0 hreg hF hLF hLE hinv hsb hain hz
    (by omega) hap hlive hqc hc40 hq hof hstkA
  exact ⟨⟨fw2_keep r2 (by omega) hfw, r1, r3, r5, r6, hlc, hql, hnc, hqc⟩,
    r4 l hlc, r2⟩

set_option maxRecDepth 20000 in
/-- the round facts after a callee writing `z` -/
theorem after_z (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {b1 b2 p l c q ql qc : Nat}
    (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(p, p + 8 * c)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(p, p + 8 * c)] ++ stkWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M')
    {p' l' c' : Nat} (hlive : NatLive M' R L2 p' c') (hc40 : c' < 2 ^ 40) (hp : p' < 2 ^ 64)
    (hof : (p' = p ∧ c' = c) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1))
    (hstkA : ¬ (p' = p ∧ c' = c) → 0 < c' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart p' (8 * c') (stW M' st) (8 * stCap M' st))
    (hl : l' ≤ c') (hc : NW n + 1 ≤ c') :
    Mid R kc L s zp zc st xp xl xc n M' L2 b2 p' l' c' q ql qc ∧
      (∀ k, k ≤ qc → M'.readLE q (8 * k) = M.readLE q (8 * k)) ∧
      (∀ a, (s.regs 4).toNat - 144 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 → M'.readLE a 8 = M.readLE a 8) := by
  obtain ⟨hfw, hrt, hz, hzz, hap, -, hqlc, hnc, hqc⟩ := hmid
  have hsp := sp_K hpre
  have hap' : Apart q (8 * qc) p (8 * c) := by unfold Apart at hap ⊢; omega
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := after_core hpre hrt hS' hstk habove hz (by omega) hreg hF hLF hLE hinv hsb hain
    hzz hqc hap' hlive (by omega) hc40 hp hof hstkA
  exact ⟨⟨fw2_keep r2 (by omega) hfw, r1, r5, r3, by unfold Apart at r6 ⊢; omega, hl, hqlc, hc, hqc⟩, r4, r2⟩

set_option maxRecDepth 20000 in
/-- a callee whose frame misses the stack object leaves it alone -/
theorem nostk (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc)
    (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(t, t + 8 * tc)]))
    (hLF : LiveFrame M M' L1 [(t, t + 8 * tc)]) (hLE : LiveExt R L1 L2) :
    MemFrame M M' (R.rt ++ win S' stk above ++ [(t, t + 8 * tc)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stkWs M st) ∧ StackBack R L1 L2 st M M' ∧ ArrIn L2 st M M' ∧
      stCap M' st = stCap M st := by
  have hsp := sp_K hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hpre
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw
  have hok := hrt.2.2.2.2.2.1
  have hsh : Held R L1 st 24 := hok.2.1
  have ht9 := ht.2.2.2.2.2.2.2.2.1.1
  unfold Apart at ht9
  have hrd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := by
    intro j hj
    refine held_bytes (hsh.sub (by omega) (by omega)) hF hLF fun i hi => ⟨?_, ?_⟩
    · simp only [win, hS', outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
  have e0 : stW M' st = stW M st := by have := hrd 0 (by omega); simpa only [Nat.add_zero] using this
  have e1 : stLen M' st = stLen M st := hrd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hrd 16 (by omega)
  exact ⟨hF.mono fun a k h => by simp only [outside_append] at h ⊢; exact h.1,
    FvModexp.LiveFrame.mono_ws hLF fun a k h => by simp only [outside_append] at h ⊢; exact h.1,
    stackBack_hdr hok hF e0 e1 e2 hLE, fun h => absurd ⟨e0, e2⟩ h, e2⟩

end

end FvModexp.Amd64.ModInv
