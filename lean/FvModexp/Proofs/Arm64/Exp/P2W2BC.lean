import FvModexp.Proofs.Arm64.Exp.P2W2LK
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the loop body's shared context `BF` and its transport through a callee
(agent infra)

`BF … M L1 b1 zzp bp` = `WC` at the loop level `ℓL`, the frame slots `ESl` and the table / `zz` facts `TZ` — what
every point of the loop body has. `BF.call`: through a callee at `SP = sp` (window `[sp - stk, sp - 8) ∪ [sp + 8,
sp + above)`, `above ≤ 88`) that writes a destination buffer `(pd, cd)` of either class and restores the stack
(`StackBackL`): `BF` at the new memory, the window slots from `sp + 88` on, and every other buffer (class kept, bytes
kept) — the pattern of each of the body's six calls.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the common facts of every point of the loop body -/
structure BF (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 zzp bp : Nat) : Prop where
  wc : WC R L K g sp st zp zc s.mem M L1 b1 (ℓL (stLen s.mem st) lm)
  esl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st)
  tz : TZ R L s.mem M L1 st sp zzp bp lm (natVal s.mem xp xl)

/-- a normalised nat `p[0:l]` (cap `c`) of odd value `v` -/
@[reducible] def NV (M : Memory) (p l c v : Nat) : Prop :=
  l ≤ c ∧ natVal M p l = v ∧ NatNorm M p l ∧ v % 2 = 1

theorem nlen_bd {M : Memory} {p l n : Nat} (hN : NatNorm M p l) (hv : natVal M p l < 2 ^ (64 * n)) : l ≤ n := by
  rw [← SubMod2N.norm_nlen M p l hN]
  exact Exp.nlen_le_iff.2 (by simp only [Exp.B]; rw [← Nat.pow_mul]; exact hv)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

/-- an entry-relative scratch nat is apart from the stack header -/
theorem scr_hdr (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {L1 : List (Nat × Nat)} {M : Memory} {t k : Nat}
    (hs : Scr R L L1 s.mem M st t k) : Apart t (8 * k) st 24 := by
  have hsf : Apart st 24 (free s.mem st).1 (free s.mem st).2 :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases hs.loc with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · simp only [Apart] at hsf ⊢; omega
  · exact fresh_held_apart hin hap hP.stk0.2.1

/-- `UB` through a callee that restores the stack -/
theorem UB.call {M M' : Memory} {L1 L2 : List (Nat × Nat)} {zzp bp p c : Nat}
    (hu : UB R L K g sp st zp zc M L1 zzp bp lm p c) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hx : LiveExt R L1 L2) (hb : StackBack R L1 L2 st M M') : UB R L K g sp st zp zc M' L2 zzp bp lm p c := by
  refine ⟨hu.c40, fun hc => ?_, hu.org, fun hc => ?_, fun hc => ?_⟩
  rotate_left 2
  · rcases hb.2.2 with ⟨e0, e2⟩ | ⟨hin, hap⟩
    · rw [e0, e2]; exact hu.rs hc
    · exact fun _ => Or.inr (fresh_held_apart hin hap (hu.live hc).2.1).symm
  · obtain ⟨a1, a2, a3, a4⟩ := hu.live hc
    exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hu.ap hc
    refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
    have hlc := hb.1.2.2.2.2.2.1
    obtain ⟨-, hl, hk⟩ := hb
    rcases hk with ⟨e0, e2⟩ | ⟨hin, hap⟩
    · simp only [e0, e2, hl]; exact a5
    · have := fresh_held_apart hin hap (hu.live hc).2.1
      show Apart p (8 * c) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
      unfold Apart at this ⊢; omega

theorem BC.call {M M' : Memory} {L1 L2 : List (Nat × Nat)} {zzp bp : Nat} {u : Bool} {p c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u p c) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hx : LiveExt R L1 L2) (hb : StackBack R L1 L2 st M M') : BC R L K g sp st zp zc M' L2 zzp bp lm u p c := by
  cases u
  · exact h
  · exact UB.call h hacc hx hb

/-- a buffer (positive cap) is held, apart from the window, the header and the free part -/
theorem BC.out (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {zzp bp X : Nat} (htz : TZ R L s.mem M L1 st sp zzp bp lm X) {u : Bool} {p c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u p c) (hc : 0 < c) :
    Held R L1 p (8 * c) ∧ Apart p (8 * c) (sp - K) (K + 560) ∧ Apart p (8 * c) st 24 ∧
      Outside p (8 * c) [(stW M st + 8 * stLen M st, stW M st + 8 * stCap M st)] := by
  cases u
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨htz.zscr.held, scr_win hP htz.zscr, scr_hdr hP htz.zscr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]
    rcases htz.zbu with ⟨c1, c2⟩ | hap
    · omega
    · unfold Apart at hap; omega
  · obtain ⟨a1, a3, -, -, a5, -, -⟩ := h.ap hc
    refine ⟨(h.live hc).2.1, a1, a3, ?_⟩
    simp only [Apart] at a5
    simp only [outside_cons, outside_nil, and_true]
    omega

/-- the destination of a callee (either class) lies in `ZS` or is fresh (the `WC.call` side conditions) -/
theorem BC.zs (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {zzp bp X : Nat} (htz : TZ R L s.mem M L1 st sp zzp bp lm X) {u : Bool} {p c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u p c) (hc : 0 < c) :
    (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(p, p + 8 * c)]) ∧
    (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(p, p + 8 * c)]) := by
  have hloc : (p = zp ∧ c = zc) ∨ (stW s.mem st + 8 * stLen s.mem st ≤ p ∧ p + 8 * c ≤ stW s.mem st + 8 * stCap s.mem st)
      ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L) := by
    cases u
    · obtain ⟨rfl, rfl⟩ := h
      rcases htz.zscr.loc with ⟨-, l1, l2⟩ | hf
      · exact Or.inr (Or.inl ⟨l1, l2⟩)
      · exact Or.inr (Or.inr hf)
    · rcases h.org with ho | ⟨-, hf⟩
      · exact Or.inl ho
      · exact Or.inr (Or.inr hf)
  refine ⟨fun a k ho hz => ?_, fun a k hin hz => ?_⟩ <;>
    simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at hz ⊢
  · rcases hloc with ⟨rfl, rfl⟩ | ⟨l1, l2⟩ | ⟨hin, -⟩
    · exact hz.1
    · omega
    · have := hin.apart ho; unfold Apart at this; omega
  · rcases hloc with ⟨rfl, rfl⟩ | ⟨l1, l2⟩ | ⟨-, hap⟩
    · exact hz.1
    · omega
    · have := hap.apart_of_inRanges hin; omega

set_option maxRecDepth 20000 in
/-- `TZ` through a callee that restores the stack and keeps the header slots and `buf` -/
theorem TZ.call {m0 M M' : Memory} {L1 L2 : List (Nat × Nat)} {zzp bp X : Nat}
    (h : TZ R L m0 M L1 st sp zzp bp lm X) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hx : LiveExt R L1 L2) (hb : StackBack R L1 L2 st M M')
    (hrd : ∀ a k, (sp + 320 ≤ a ∧ a + k ≤ sp + 416) ∨ (bp ≤ a ∧ a + k ≤ bp + 8 * P2Pre.NB 4 lm) →
      M'.readLE a k = M.readLE a k) :
    TZ R L m0 M' L2 st sp zzp bp lm X := by
  refine ⟨fun j hj => ?_, Scr.mono h.bscr hacc hx, P2Pre.bu_back h.bbu h.bscr.held hb, Scr.mono h.zscr hacc hx,
    P2Pre.bu_back h.zbu h.zscr.held hb, h.zb⟩
  obtain ⟨d0, d1, d2, d3, d4⟩ := h.pw j hj
  have r0 := hrd (sp + 320 + 24 * j) 8 (Or.inl ⟨by omega, by omega⟩)
  have r1 := hrd (sp + 320 + 24 * j + 8) 8 (Or.inl ⟨by omega, by omega⟩)
  have r2 := hrd (sp + 320 + 24 * j + 16) 8 (Or.inl ⟨by omega, by omega⟩)
  have hjW : (j + 1) * P2Pre.W lm ≤ P2Pre.NB 4 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjW' : j * P2Pre.W lm + P2Pre.W lm = (j + 1) * P2Pre.W lm := by rw [Nat.succ_mul]
  have hjj : j * P2Pre.W lm + P2Pre.W lm ≤ P2Pre.NB 4 lm := by rw [hjW']; exact hjW
  rw [← r1] at d2 d3 d4
  refine ⟨r0.trans d0, r2.trans d1, d2, ?_, ?_⟩
  · show M'.readLE _ _ = _
    rw [hrd _ _ (Or.inr ⟨by omega, by omega⟩)]; exact d3
  · rcases Nat.eq_zero_or_pos (M'.readLE (sp + 320 + 24 * j + 8) 8) with h0 | h0
    · exact Or.inl h0
    rcases d4 with d4 | d4
    · exact Or.inl d4
    · right; rw [hrd _ _ (Or.inr ⟨by omega, by omega⟩)]; exact d4

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`BF` through a callee** writing the buffer `(pd, cd)` (see the module doc) -/
theorem BF.call (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {ret : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 zzp bp : Nat} (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp)
    {v : Bool} {pd cd : Nat} (hd : BC R L K g sp st zp zc M L1 zzp bp lm v pd cd) (hcd : 0 < cd)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    BF R L K g sp st zp zc xp xl xc yp yl lm ret s M' L2 b2 zzp bp ∧
    (∀ a k, sp + 88 ≤ a → a + k ≤ sp + 560 → M'.readLE a k = M.readLE a k) ∧
    (∀ (w : Bool) (q c : Nat), BC R L K g sp st zp zc M L1 zzp bp lm w q c → 0 < c →
      Apart q (8 * c) pd (8 * cd) → BC R L K g sp st zp zc M' L2 zzp bp lm w q c ∧
        ∀ a k, q ≤ a → a + k ≤ q + 8 * c → M'.readLE a k = M.readLE a k) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hlp : 0 < ℓL (stLen s.mem st) lm := by have := hP.2.2.2.2.2.1; simp only [ℓL, ℓZ, ℓR, W]; omega
  have hwo := WC.win_out hP hB.wc hlp
  obtain ⟨dH, dW, dS, dF⟩ := BC.out hP hB.tz hd hcd
  unfold Apart at dW dS
  simp only [outside_cons, outside_nil, and_true] at dF
  have hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w := hF.accessible
  have hF' : MemFrame M M' (R.rt ++ ([(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++
      stkWs M st)) := by simpa only [List.append_assoc] using hF
  -- a held range outside the callee's writes keeps its bytes
  have hkeep : ∀ a k, Held R L1 a k → Outside a k [(sp - stk, sp - 8), (sp + 8, sp + above)] →
      Outside a k [(pd, pd + 8 * cd)] → Outside a k (stkWs M st) → M'.readLE a k = M.readLE a k := by
    intro a k hh h1 h2 h3
    rcases hh with hin | hrt
    · exact hLF.readLE a k hin (by rw [outside_append]; exact ⟨h2, h3⟩)
    · exact hF'.readLE a k (by rw [outside_append, outside_append, outside_append]; exact ⟨hrt, ⟨h1, h2⟩, h3⟩)
  -- window slots
  have hslot : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 88 ≤ a ∧ a + k ≤ sp + 560) →
      M'.readLE a k = M.readLE a k := by
    intro a k ha
    have h0 := hwo a k (by omega) (by omega)
    rw [outside_append] at h0
    exact hF.readLE a k (by
      rw [outside_append, outside_append, outside_append]
      refine ⟨⟨⟨h0.1, ?_⟩, ?_⟩, h0.2⟩ <;> simp only [outside_cons, outside_nil, and_true] <;> omega)
  obtain ⟨zr, zl⟩ := BC.zs hP hB.tz hd hcd
  have hw : WC R L K g sp st zp zc s.mem M' L2 b2 (ℓL (stLen s.mem st) lm) := by
    refine hB.wc.call (ws := [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st)
      (by simpa only [List.append_assoc] using hF) hLF hrg ?_ ?_ hx hinv
      hsb.1.1 (hsb.1.2.1.trans hB.wc.len) (Nat.le_refl _) hsb.1.2.2 hsb.2
    · intro a k o1 o2 o3 o4
      rw [outside_append, outside_append]
      refine ⟨⟨?_, zr a k o1 o4⟩, o3⟩
      simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢; omega
    · intro a k hin ho
      rw [outside_append]
      exact ⟨zl a k hin ho, stk_out hB.wc (Or.inl hin) ho⟩
  -- the table / zz buffer
  have hbW := scr_win hP hB.tz.bscr
  have hbS := scr_hdr hP hB.tz.bscr
  unfold Apart at hbW hbS
  have hbD : Apart bp (8 * P2Pre.NB 4 lm) pd (8 * cd) := by
    cases v
    · obtain ⟨rfl, rfl⟩ := hd; exact hB.tz.zb.symm
    · exact (hd.ap hcd).2.2.2.2.2.2.symm
  unfold Apart at hbD
  have hbF : ∀ a k, bp ≤ a → a + k ≤ bp + 8 * P2Pre.NB 4 lm → Outside a k (stkWs M st) := by
    intro a k h1 h2
    simp only [stkWs, outside_cons, outside_nil, and_true]
    refine ⟨by omega, ?_⟩
    rcases hB.tz.bbu with ⟨c1, c2⟩ | hap
    · omega
    · unfold Apart at hap; have := hsb.1.1; omega
  have htz : TZ R L s.mem M' L2 st sp zzp bp lm (natVal s.mem xp xl) := by
    refine TZ.call hB.tz hacc hx hsb.1 fun a k ha => ?_
    rcases ha with ha | ⟨h1, h2⟩
    · exact hslot a k (by omega)
    · exact hkeep a k (hB.tz.bscr.held.sub h1 h2)
        (by simp only [outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega) (hbF a k h1 h2)
  refine ⟨⟨hw, ESl.keep hB.esl (fun a k ha => hslot a k (by omega)) (by omega), htz⟩,
    fun a k h1 h2 => hslot a k (by omega), fun w q c hq hc hqd => ⟨BC.call hq hacc hx hsb.1, fun a k h1 h2 => ?_⟩⟩
  obtain ⟨qH, qW, qS, qF⟩ := BC.out hP hB.tz hq hc
  unfold Apart at qW qS hqd
  simp only [outside_cons, outside_nil, and_true] at qF
  exact hkeep a k (qH.sub h1 h2) (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega)

end

end FvModexp.Arm64.P2W2
