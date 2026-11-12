import FvModexp.Proofs.Arm64.Exp.EvRel

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the function's local nats and the generic callee step (agent infra)

Every local nat of `nat.expNNEven` (the scratch nats of `stk.nat`, the results of the callees) is

* `Loc R L m0 st t k`: located, relative to the ENTRY (memory `m0`, live set `L`), in the entry free part of the stack
  or fresh (in the runtime ranges, apart from all of `L`) — stable for the whole function; it gives apartness from
  the window, the stack header, the guard word and `z`'s array (`Loc.ap`), and that the array is outside every range
  the CALLER may observe (`Loc.sub` / `Loc.subL`: the obligations of `WC.call` for a callee writing it);
* `Ob R L1 st M t k` (EvRel): held, in the used part of the current stack array or apart from it.

`DL` = an array with these facts (a destination), `LN` = `DL` plus length, value and normalisation (a live value).
`stepC`: the context `WC`, the slots and every `LN` apart from the callee's destination survive a callee step
(callee window, destination `(pd, cd)`, the stack's writable ranges, `StackBackL`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- entry-relative location of a local array (see the module doc) -/
@[reducible] def Loc (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st t k : Nat) : Prop :=
  (0 < stCap m0 st ∧ stW m0 st + 8 * stLen m0 st ≤ t ∧ t + 8 * k ≤ stW m0 st + 8 * stCap m0 st) ∨
    (InRanges t (8 * k) R.rt ∧ ApartAll t (8 * k) L)

/-- a destination array `p[0:c]` at memory `M` (live set `L1`) -/
@[reducible] def DL (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L1 p c ∧ (0 < c → Loc R L m0 st p c ∧ Ob R L1 st M p c)

/-- a live local nat `p[0:l]` (cap `c`) of value `v` -/
@[reducible] def LN (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p l c v : Nat) : Prop :=
  DL R L m0 st M L1 p c ∧ l ≤ c ∧ natVal M p l = v ∧ NatNorm M p l

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the apartness facts of a located array -/
theorem Loc.ap (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {t k : Nat}
    (h : Loc R L s.mem st t k) :
    Apart t (8 * k) (sp - K) (K + 448) ∧ Apart t (8 * k) st 24 ∧ Apart t (8 * k) (g + 16) 8 ∧
      (0 < zc → Apart t (8 * k) zp (8 * zc)) := by
  have hout := hP.win_rt
  have hgo : Outside (g + 16) 8 ((sp - K, sp + 448) :: R.rt) := hP.1.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have harr := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsf := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsok := hP.stk0
  rcases h with ⟨c0, l1, l2⟩ | ⟨hin, hap⟩
  · obtain ⟨a1, a2⟩ := harr c0
    simp only [Apart] at a1 a2 hsf ⊢
    refine ⟨by omega, by omega, by omega, fun hz0 => ?_⟩
    have := (hz hz0).1.2.2.2
    simp only [Apart] at this; omega
  · simp only [outside_cons] at hgo
    exact ⟨(hin.apart hout).symm, hfresh hsok.2.1 hap hin, (hin.apart hgo.2).symm,
      fun hz0 => hfresh (hz hz0).1.1 hap hin⟩

/-- the stack's array is `0` when empty (entry fact, kept or fresh with `0 < cap`) -/
theorem WC.cap0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    stCap M st = 0 → stW M st = 0 := by
  intro h0
  by_cases e : stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  · rw [e.1]; exact hP.cap0 (by rw [← e.2]; exact h0)
  · have := (h.ain e).2; omega

/-- `WC.call`'s obligations for a callee writing a located array -/
theorem Loc.sub {t k : Nat} (h : Loc R L s.mem st t k) :
    ∀ a n, Outside a n R.rt → Outside a n (ZS zp zc st s.mem) → Outside a n [(t, t + 8 * k)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨-, l1, l2⟩ | ⟨hin, -⟩
  · omega
  · have := hin.apart h1; unfold Apart at this; omega

theorem Loc.subL {t k : Nat} (h : Loc R L s.mem st t k) :
    ∀ a n, InRanges a n L → Outside a n (ZS zp zc st s.mem) → Outside a n [(t, t + 8 * k)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨-, l1, l2⟩ | ⟨-, hap⟩
  · omega
  · have := hap.apart_of_inRanges h1; omega

end

/-- a fresh array (relative to `L1`, apart from the final stack array when that changed) is an `Ob` -/
theorem ob_fresh {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {p c : Nat}
    (hok : StkOK M R L1 st) (hc0 : stCap M st = 0 → stW M st = 0) (hin : InRanges p (8 * c) R.rt)
    (hap : ApartAll p (8 * c) L1) (hh : Held R L2 p (8 * c)) (hrs : ResSep M M' st p c) (hc : 0 < c) :
    Ob R L2 st M' p c := by
  refine ⟨hh, Or.inr ?_⟩
  by_cases e : stW M' st = stW M st ∧ stCap M' st = stCap M st
  · rw [e.1, e.2]
    rcases Nat.eq_zero_or_pos (stCap M st) with c0 | c0
    · rw [c0, hc0 c0]; unfold Apart; omega
    · exact hfresh (hok.2.2.2.2.1 c0).2.1 hap hin |>.symm |> fun h => h.symm
  · exact hrs hc e

/-- `LN` through a step keeping its bytes -/
theorem LN.keep {R : RtInv} {L : List (Nat × Nat)} {m0 : Memory} {st : Nat} {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {p l c v : Nat} (h : LN R L m0 st M L1 p l c v) (hx : LiveExt R L1 L2)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hb : 0 < c → ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k)
    (hob : 0 < c → Ob R L2 st M' p c) : LN R L m0 st M' L2 p l c v := by
  obtain ⟨⟨c40, hlv, hlo⟩, hlc, hv, hn⟩ := h
  refine ⟨⟨c40, fun hc => ?_, fun hc => ⟨(hlo hc).1, hob hc⟩⟩, hlc, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hlv hc
    exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩
  · rcases Nat.eq_zero_or_pos c with c0 | c0
    · have : l = 0 := by omega
      subst this
      rw [← hv]; exact Memory.readLE_congr fun i hi => absurd hi (by omega)
    · rw [← hv]; exact hb c0 _ _ (Nat.le_refl _) (by omega)
  · rcases hn with h0 | hne
    · exact Or.inl h0
    · rcases Nat.eq_zero_or_pos c with c0 | c0
      · exact Or.inl (by omega)
      · right; rw [hb c0 _ _ (by omega) (by omega)]; exact hne

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- **the generic callee step** (see the module doc): the destination `(pd, cd)` is a located array or `z`'s -/
theorem stepC (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    (hds : ∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(pd, pd + 8 * cd)])
    (hdl : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(pd, pd + 8 * cd)])
    (hcd : 0 < cd) (hdw : Apart pd (8 * cd) (sp - K) (K + 448))
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    WC R L K g sp st zp zc s.mem M' L2 b2 ℓ ∧
    (∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 88 ≤ a ∧ a + k ≤ sp + 448) → M'.readLE a k = M.readLE a k) ∧
    (∀ q l c v, LN R L s.mem st M L1 q l c v → (0 < c → Apart q (8 * c) pd (8 * cd)) →
      LN R L s.mem st M' L2 q l c v) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hzs : ∀ a k, sp - K ≤ a → a + k ≤ sp + 448 → Outside a k [(pd, pd + 8 * cd)] := by
    intro a k h1 h2
    simp only [outside_cons, outside_nil, and_true]
    have := hdw; unfold Apart at this; omega
  have hk := keepC hP h hF hstk habove hzs
  have hw : WC R L K g sp st zp zc s.mem M' L2 b2 ℓ := by
    refine h.call (ws := [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st)
      (by simpa only [List.append_assoc] using hF) hLF hrg ?_ ?_ hx hinv
      hsb.1.1 (hsb.1.2.1.trans h.len) (Nat.le_refl _) hsb.1.2.2 hsb.2
    · intro a k o1 o2 o3 o4
      rw [outside_append, outside_append]
      refine ⟨⟨?_, hds a k o1 o4⟩, o3⟩
      simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢; omega
    · intro a k hin ho
      rw [outside_append]
      exact ⟨hdl a k hin ho, stk_out h (Or.inl hin) ho⟩
  have hlc := h.sok.2.2.2.2.2.1
  refine ⟨hw, hk, fun q l c v hq hqd => hq.keep hx hF.accessible (fun c0 a k h1 h2 => ?_)
    (fun c0 => ((hq.1.2.2 c0).2).back hx hsb.1)⟩
  obtain ⟨w1, w2, -, -⟩ := Loc.ap hP (hq.1.2.2 c0).1
  have hob := (hq.1.2.2 c0).2
  have hout := hob.out hlc w2
  unfold Apart at w1
  simp only [stkWs, outside_cons, outside_nil, and_true] at hout
  refine keepH (cw := [(sp - stk, sp - 8), (sp + 8, sp + above)]) hF hLF (hob.1.sub h1 h2) ?_ ?_ ?_
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]
    have := hqd c0; unfold Apart at this; omega
  · simp only [stkWs, outside_cons, outside_nil, and_true]; omega

end

/-- a callee that does not touch the stack (writes: runtime, its window `cw`, the destination): the frame in the
`stepC` form and `StackBackL` (array and length kept) -/
theorem nonStk {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {cw : List (Nat × Nat)}
    {pd cd : Nat} (hok : StkOK M R L1 st) (hx : LiveExt R L1 L2)
    (hF : MemFrame M M' (R.rt ++ cw ++ [(pd, pd + 8 * cd)])) (hLF : LiveFrame M M' L1 [(pd, pd + 8 * cd)])
    (h1 : Outside st 24 cw) (h2 : Outside st 24 [(pd, pd + 8 * cd)]) :
    MemFrame M M' (R.rt ++ cw ++ [(pd, pd + 8 * cd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st) ∧ StackBackL R L1 L2 st M M' ∧
      (stW M' st = stW M st ∧ stCap M' st = stCap M st) := by
  have hF0 : MemFrame M M' (R.rt ++ cw ++ [(pd, pd + 8 * cd)] ++ []) := by simpa only [List.append_nil] using hF
  have hL0 : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ []) := by simpa only [List.append_nil] using hLF
  have hhd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    keepH hF0 hL0 (hok.2.1.sub (by omega) (by omega)) (h1.of_sub (by omega) (by omega))
      (h2.of_sub (by omega) (by omega)) (by simp only [outside_nil])
  have e0 : stW M' st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen M' st = stLen M st := hhd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hhd 16 (by omega)
  refine ⟨hF.mono fun a k ho => by rw [outside_append] at ho; exact ho.1,
    Expmc.liveFrame_widen hLF fun a k ho => by rw [outside_append] at ho; exact ho.1,
    ⟨⟨stkOK_hdr hok hF e0 e1 e2 hx, e1, Or.inl ⟨e0, e2⟩⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩, e0, e2⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the result of a callee (`NatRes`: the destination `(pd, cd)` reused, or fresh) is a live local nat -/
theorem LN.of_res (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    (hd : DL R L s.mem st M L1 pd cd) {M' : Memory} {L2 : List (Nat × Nat)} {need p' l' c' v : Nat}
    (hr : ExpHyp.NatRes R L1 L2 M' pd cd need p' l' c' v) (hx : LiveExt R L1 L2)
    (hsb : StackBackL R L1 L2 st M M') (hrs : ResSep M M' st p' c') : LN R L s.mem st M' L2 p' l' c' v := by
  obtain ⟨hv, hn, hlc, hc40, hlv, hke, hfr⟩ := hr
  refine ⟨⟨hc40, hlv, fun hc => ?_⟩, hlc, hv, hn⟩
  rcases Nat.lt_or_ge cd need with hlt | hge
  · obtain ⟨hin, hap⟩ := hfr hlt hc
    exact ⟨Or.inr ⟨hin, fun r hr => hap r (h.le.mem_old hr)⟩,
      ob_fresh h.sok (WC.cap0 hP h) hin hap (hlv hc).2.1 hrs hc⟩
  · obtain ⟨rfl, rfl⟩ := hke hge
    obtain ⟨l1, o1⟩ := hd.2.2 hc
    exact ⟨l1, o1.back hx hsb.1⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc : Nat} {m0 : Memory}

/-- a scratch nat of `stk.nat` (at level `ℓb`, now level `ℓ ≥ ℓb + k`) is a destination -/
theorem DL.of_scr {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ)
    {p k ℓb : Nat} (hs : Scr R L L1 m0 M st p k) (hp : p = stW M st + 8 * ℓb) (hl : ℓb + k ≤ ℓ)
    (hk : k < 2 ^ 40) : DL R L m0 st M L1 p k := by
  have hlen := h.len
  exact ⟨hk, fun _ => ⟨hs.al, hs.held, hs.acc, hs.b48⟩, fun _ => ⟨hs.loc, hs.held, Or.inl ⟨by omega, by omega⟩⟩⟩

/-- a new scratch nat (relative to the call memory `M`, live set `L1`) is apart from every live local of `M` -/
theorem Scr.apartLN {M M' : Memory} {L1 L2 : List (Nat × Nat)} {t k : Nat} (hs : Scr R L1 L2 M M' st t k)
    (hlc : stLen M st ≤ stCap M st) {q l c v : Nat} (hq : LN R L m0 st M L1 q l c v) (hc : 0 < c) :
    Apart t (8 * k) q (8 * c) := by
  have hob := (hq.1.2.2 hc).2
  exact hs.apart hob.1 fun _ => hob.free hlc

end

end FvModexp.Arm64.ExpEven
