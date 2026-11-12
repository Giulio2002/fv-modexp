import FvModexp.Proofs.Arm64.Exp.EvPP
import FvModexp.Proofs.Arm64.Exp.EvEnt

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the shared relations of every segment (ROW-TIME rule: every segment imports this
module directly) (agent infra)

* `wc_init` (the context `WC` after the function's own frame writes `FW sp`), `win_out0` (`WC.win_out` without
  `0 < ℓ`, from `stCap = 0 → stW = 0`), `keepC` (a callee frame keeps the slots `[sp - 8, sp + 8)` and
  `[sp + 128, sp + 448)`), `tz_lt`;
* `Ob R L1 st M t k`: a nat array `[t, t + 8k)` the function keeps using (scratch nats of `stk.nat`, fresh results of
  callees): held in the live set, and either inside the USED part of the stack's current array or apart from the
  whole current array. It survives every callee with `StackBack` (`Ob.back`) and the function's own `stk.nat`
  (`Ob.mono`: level up, array kept or fresh), gives apartness from the free part (`Ob.free`), and a held range apart
  from a callee's explicit writes keeps its bytes (`keepH`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem tz_lt {X ml : Nat} (h0 : 0 < X) (h : X < 2 ^ (64 * ml)) : Exp.tz X < 64 * ml := by
  have hs := (Exp.tz_spec h0).1
  have hq : 0 < X / 2 ^ Exp.tz X := by
    rcases Nat.eq_zero_or_pos (X / 2 ^ Exp.tz X) with e | e
    · rw [e, Nat.mul_zero] at hs; omega
    · exact e
  have : 2 ^ Exp.tz X ≤ X := by
    calc 2 ^ Exp.tz X ≤ 2 ^ Exp.tz X * (X / 2 ^ Exp.tz X) := Nat.le_mul_of_pos_right _ hq
      _ = X := hs.symm
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt this h)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

theorem EPre.cap0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) :
    stCap s.mem st = 0 → stW s.mem st = 0 :=
  hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

/-- the context after the function's own writes (frame `FW sp`) at the entry level -/
theorem wc_init (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FW sp)) (hrg : M.regions = s.mem.regions) :
    WC R L K g sp st zp zc s.mem M L b (stLen s.mem st) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsok := hP.stk0
  unfold Apart at hstw
  have hFW : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st s.mem) → Outside a k (FW sp) := by
    intro a k ho
    simp only [WN, FW, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have hhd : Outside st 24 (FW sp) := by simp only [FW, outside_cons, outside_nil, and_true]; omega
  have e0 : stW M st = stW s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M st = stLen s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M st = stCap s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  refine ⟨hF.mono fun a k ho => hFW a k ho, LiveFrame.of_win hF (fun r hr => by
      have := hLs r hr; simp only [FW, outside_cons, outside_nil, and_true] at this ⊢; omega), hrg,
    LiveExt.refl R L, Expmc.inv_frame hF ?_ hinv, stkOK_hdr hsok hF e0 e1 e2 (LiveExt.refl R L), e1, Nat.le_refl _,
    hsok.2.2.2.2.2.1, Or.inl ⟨e0, e2⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩
  intro r hr
  right
  simp only [FW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout.of_sub (show sp - K ≤ sp - 8 by omega) (show sp - 8 + (sp + 328 - (sp - 8)) ≤ sp - K + (K + 448) by omega)
  · exact hout.of_sub (show sp - K ≤ sp + 344 by omega)
      (show sp + 344 + (sp + 448 - (sp + 344)) ≤ sp - K + (K + 448) by omega)

variable {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the window is outside the runtime ranges and the stack's writable ranges (any level) -/
theorem win_out0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ a k, sp - K ≤ a → a + k ≤ sp + 448 → Outside a k (R.rt ++ stkWs M st) := by
  intro a k h1 h2
  rcases Nat.eq_zero_or_pos ℓ with h0 | h0
  · have hout := hP.win_rt
    have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have harr := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hK := hP.1.2.2.2.2.2.2.2.2.1
    have hc0 := hP.cap0
    rw [outside_append]
    refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
    simp only [stkWs, outside_cons, outside_nil, and_true]
    unfold Apart at hstw
    refine ⟨by omega, ?_⟩
    rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rcases Nat.eq_zero_or_pos (stCap s.mem st) with c0 | c0
      · have := hc0 c0; rw [e1, e2, this, c0]; omega
      · have := (harr c0).1
        rw [← e1, ← e2] at this; unfold Apart at this; omega
    · have := hin.apart (hout.of_sub (a := a) (n := k) (by omega) (by omega)); unfold Apart at this
      have := h.sok.2.2.2.2.2.1; omega
  · exact h.win_out hP h0 a k h1 h2

/-- a callee frame (runtime, the callee window `[sp - stk, sp - 8) ∪ [sp + 8, sp + above)`, extra ranges `zs`
apart from the window, the stack's writable ranges) keeps the slots `[sp - 8, sp + 8)` and `[sp + 128, sp + 448)` -/
theorem keepC (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory} {stk above : Nat} {zs : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ zs ++ stkWs M st))
    (hstk : stk ≤ K) (habove : above ≤ 128)
    (hzs : ∀ a k, sp - K ≤ a → a + k ≤ sp + 448 → Outside a k zs) :
    ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 128 ≤ a ∧ a + k ≤ sp + 448) → M'.readLE a k = M.readLE a k := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  intro a k ha
  refine hF.readLE a k ?_
  have h1 := win_out0 hP h a k (by omega) (by omega)
  have h2 := hzs a k (by omega) (by omega)
  rw [outside_append] at h1
  rw [outside_append, outside_append, outside_append]
  refine ⟨⟨⟨h1.1, ?_⟩, h2⟩, h1.2⟩
  simp only [outside_cons, outside_nil, and_true]
  omega

end


/-- a fresh range is apart from every held range -/
theorem hfresh {R : RtInv} {L : List (Nat × Nat)} {a n ptr k : Nat} (h : Held R L a n)
    (hAp : ApartAll ptr k L) (hIn : InRanges ptr k R.rt) : Apart ptr k a n := by
  rcases h with hL | ho
  · exact hAp.apart_of_inRanges hL
  · exact (hIn.apart ho).symm

/-- a nat array the function keeps using (see the module doc) -/
@[reducible] def Ob (R : RtInv) (L1 : List (Nat × Nat)) (st : Nat) (M : Memory) (t k : Nat) : Prop :=
  Held R L1 t (8 * k) ∧
    ((stW M st ≤ t ∧ t + 8 * k ≤ stW M st + 8 * stLen M st) ∨ Apart t (8 * k) (stW M st) (8 * stCap M st))

/-- `Ob` through a step where the level does not drop and the array is kept or fresh relative to `L1` -/
theorem Ob.mono {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : Ob R L1 st M t k) (hx : LiveExt R L1 L2) (hl : stLen M st ≤ stLen M' st)
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1)) :
    Ob R L2 st M' t k := by
  refine ⟨hx.held h.1, ?_⟩
  rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]
    rcases h.2 with ⟨a1, a2⟩ | a
    · exact Or.inl ⟨a1, by omega⟩
    · exact Or.inr a
  · exact Or.inr (hfresh h.1 hap hin).symm

/-- `Ob` through a callee with `StackBack` -/
theorem Ob.back {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : Ob R L1 st M t k) (hx : LiveExt R L1 L2) (hsb : StackBack R L1 L2 st M M') : Ob R L2 st M' t k :=
  h.mono hx (by rw [hsb.2.1]; exact Nat.le_refl _) hsb.2.2

/-- an `Ob` array is apart from the stack's free part -/
theorem Ob.free {R : RtInv} {L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : Ob R L1 st M t k)
    (hlc : stLen M st ≤ stCap M st) : Apart t (8 * k) (free M st).1 (free M st).2 := by
  show Apart t (8 * k) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
  rcases h.2 with ⟨a1, a2⟩ | a
  · unfold Apart; omega
  · unfold Apart at a ⊢; omega

/-- an `Ob` array is outside the stack's writable ranges when apart from the header -/
theorem Ob.out {R : RtInv} {L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : Ob R L1 st M t k)
    (hlc : stLen M st ≤ stCap M st) (hst : Apart t (8 * k) st 24) : Outside t (8 * k) (stkWs M st) := by
  have := h.free hlc
  simp only [free, Apart] at this hst
  simp only [stkWs, outside_cons, outside_nil, and_true]
  omega

/-- a held range outside a callee's explicit writes (callee window `cw`, extra ranges `zs`, the stack's writable
ranges) keeps its bytes -/
theorem keepH {R : RtInv} {L1 : List (Nat × Nat)} {M M' : Memory} {cw zs ws : List (Nat × Nat)} {a k : Nat}
    (hF : MemFrame M M' (R.rt ++ cw ++ zs ++ ws)) (hLF : LiveFrame M M' L1 (zs ++ ws))
    (hh : Held R L1 a k) (h1 : Outside a k cw) (h2 : Outside a k zs) (h3 : Outside a k ws) :
    M'.readLE a k = M.readLE a k := by
  rcases hh with hin | hrt
  · exact hLF.readLE a k hin (by rw [outside_append]; exact ⟨h2, h3⟩)
  · exact hF.readLE a k (by rw [outside_append, outside_append, outside_append]; exact ⟨⟨⟨hrt, h1⟩, h2⟩, h3⟩)

end FvModexp.Arm64.ExpEven
