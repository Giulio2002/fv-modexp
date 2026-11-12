import FvModexp.Proofs.Arm64.Exp.SlowRel

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the local buffers `z`, `zz`, `r`, `q` and the generic callee step (agent expmc)

Every local nat of `nat.expNNSlow` is one of four buffers (nat.go:742-781: `z = z.set(x)`, then `zz.sqr`, `zz.mul`,
`zz.div(stk, r, …)` rotate `z, zz, r, q`); none is stack scratch. A buffer `(p, c)` is

* `Loc R L zp zc p c`: located relative to the ENTRY live set `L`: the entry `z` array (`0 < zc`), FRESH (in the
  runtime ranges, apart from all of `L`; `c = 0` allowed: an empty runtime slice), or `nil` `(0, 0)`. It gives
  apartness from the window, the stack header, the guard word, the threshold globals and the inputs `x, y, m`
  (`Loc.ap`), and the obligations of `WC.call` for a callee writing it (`Loc.sub` / `Loc.subL`, any capacity);
* `DL` (a destination): `c < 2^40`, `NatLive`, `Loc`, `Ob` (held, apart from the CURRENT free part) and `nil` when
  empty (every empty buffer is `nil`: the initial `zz, r, q`, and a callee's empty result is its destination —
  `NatOF` needs `≥ 1`, `SqrHypG` returns `z[:0]` for an empty operand); `LN` (a
  live value) = `DL` + length, value, normalisation; `Pw` = apart when both non-empty.

`DL.back`/`LN.keep` (a callee keeps a buffer), `LN.of_res` (a callee's `NatOF` result of a destination is a live
local), `stepC2` (the context `WC`, the slots and every `LN`/`DL` apart from the destinations survive a callee with
`StackBackL` writing its window and two destinations; `stepC1` for one).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- entry-relative location of a local buffer (see the module doc) -/
@[reducible] def Loc (R : RtInv) (L : List (Nat × Nat)) (zp zc p c : Nat) : Prop :=
  (p = zp ∧ c = zc ∧ 0 < zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L) ∨ (p = 0 ∧ c = 0)

/-- a destination buffer `p[0:c]` at memory `M` (live set `L1`) -/
@[reducible] def DL (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L1 p c ∧ Loc R L zp zc p c ∧ (0 < c → Ob R L L1 st M p c) ∧ (c = 0 → p = 0)

/-- a live local nat `p[0:l]` (cap `c`) of value `v` -/
@[reducible] def LN (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p l c v : Nat) : Prop :=
  DL R L st zp zc M L1 p c ∧ l ≤ c ∧ natVal M p l = v ∧ NatNorm M p l

/-- two buffers are apart when both are non-empty -/
@[reducible] def Pw (p c q k : Nat) : Prop := 0 < c → 0 < k → Apart p (8 * c) q (8 * k)

theorem Pw.symm {p c q k : Nat} (h : Pw p c q k) : Pw q k p c := fun h1 h2 => (h h2 h1).symm

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- the apartness facts of a non-empty located buffer -/
theorem Loc.ap (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : Loc R L zp zc p c) (hc : 0 < c) :
    Apart p (8 * c) (sp - K) (K + 544) ∧ Apart p (8 * c) st 24 ∧ Apart p (8 * c) (g + 16) 8 ∧
      Apart p (8 * c) RunIface.gA 32 ∧ Apart p (8 * c) xp (8 * xl) ∧ Apart p (8 * c) yp (8 * yl) ∧
      Apart p (8 * c) mp (8 * ml) := by
  have hout := hP.win_rt
  have hsok := hP.stk0
  obtain ⟨⟨-, -, -, -, -, hgo, -⟩, -, -, -, -, -, -, hoy, -, -, -, -, -, hox, -, -, -, -, -, -, -, -, hz, hogA,
    -, -, -, -, -, -, -, -, -, -, ⟨hom, -, -, -, hzm, -⟩, -⟩ := hP
  rcases h with ⟨rfl, rfl, hz0⟩ | ⟨hin, hap⟩ | ⟨-, rfl⟩
  · obtain ⟨⟨-, o1, o2, -⟩, -, -, -, a1, a2, a3, a4⟩ := hz hz0
    exact ⟨o1, o2, a1.symm, a4, a2, a3, hzm hz0⟩
  · simp only [outside_cons] at hgo
    exact ⟨(hin.apart hout).symm, hfresh hsok.2.1 hap hin, (hin.apart hgo.2).symm, hfresh hogA.1 hap hin,
      hfresh hox.1 hap hin, hfresh hoy.1 hap hin, hfresh hom.1 hap hin⟩
  · omega

/-- a located buffer (any capacity) is apart from the window -/
theorem Loc.win (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : Loc R L zp zc p c) : Apart p (8 * c) (sp - K) (K + 544) := by
  rcases Nat.eq_zero_or_pos c with c0 | c0
  · rcases h with ⟨-, e1, e2⟩ | ⟨hin, -⟩ | ⟨rfl, -⟩
    · omega
    · exact (hin.apart hP.win_rt).symm
    · unfold Apart; omega
  · exact (Loc.ap hP h c0).1

end

/-- `WC.call`'s obligations for a callee writing a located buffer -/
theorem Loc.sub {R : RtInv} {L : List (Nat × Nat)} {zp zc st : Nat} {m0 : Memory} {p c : Nat}
    (h : Loc R L zp zc p c) :
    ∀ a n, Outside a n R.rt → Outside a n (ZS zp zc st m0) → Outside a n [(p, p + 8 * c)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨rfl, rfl, -⟩ | ⟨hin, -⟩ | ⟨rfl, rfl⟩
  · exact h2.1
  · have := hin.apart h1; unfold Apart at this; omega
  · omega

theorem Loc.subL {R : RtInv} {L : List (Nat × Nat)} {zp zc st : Nat} {m0 : Memory} {p c : Nat}
    (h : Loc R L zp zc p c) :
    ∀ a n, InRanges a n L → Outside a n (ZS zp zc st m0) → Outside a n [(p, p + 8 * c)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨rfl, rfl, -⟩ | ⟨-, hap⟩ | ⟨rfl, rfl⟩
  · exact h2.1
  · have := hap.apart_of_inRanges h1; omega
  · omega

/-- a destination through a callee keeping the stack (`StackBack`) -/
theorem DL.back {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {p c : Nat} (h : DL R L st zp zc M L1 p c) (hx : LiveExt R L1 L2)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hsb : StackBack R L1 L2 st M M') :
    DL R L st zp zc M' L2 p c := by
  obtain ⟨c40, hlv, hloc, hob, h0⟩ := h
  refine ⟨c40, fun hc => ?_, hloc, fun hc => (hob hc).back hx hsb, h0⟩
  obtain ⟨a1, a2, a3, a4⟩ := hlv hc
  exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩

/-- a live local through a step keeping its bytes -/
theorem LN.keep {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {p l c v : Nat} (h : LN R L st zp zc M L1 p l c v) (hx : LiveExt R L1 L2)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hsb : StackBack R L1 L2 st M M')
    (hb : 0 < c → ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k) :
    LN R L st zp zc M' L2 p l c v := by
  obtain ⟨hd, hlc, hv, hn⟩ := h
  refine ⟨hd.back hx hacc hsb, hlc, ?_, ?_⟩
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

/-- a fresh non-empty array (relative to `L1`; apart from the final stack array when that changed) is an `Ob` -/
theorem ob_fresh {R : RtInv} {L L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {p c : Nat}
    (hok : StkOK M R L1 st) (hc0 : stCap M st = 0 → stW M st = 0) (hsb : StackBack R L1 L2 st M M')
    (hin : InRanges p (8 * c) R.rt) (hap : ApartAll p (8 * c) L1) (hh : Held R L2 p (8 * c))
    (hrs : ResSep M M' st p c) (hc : 0 < c) : Ob R L L2 st M' p c := by
  have hlc' := hsb.1.2.2.2.2.2.1
  have hA : Apart p (8 * c) (stW M' st) (8 * stCap M' st) := by
    by_cases e : stW M' st = stW M st ∧ stCap M' st = stCap M st
    · rw [e.1, e.2]
      rcases Nat.eq_zero_or_pos (stCap M st) with c0 | c0
      · rw [c0, hc0 c0]; unfold Apart; omega
      · exact hfresh (hok.2.2.2.2.1 c0).2.1 hap hin
    · exact hrs hc e
  refine ⟨hh, ?_, fun _ _ => hA⟩
  show Apart p (8 * c) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
  unfold Apart at hA ⊢; omega

/-- the result of a callee (`NatOF`: the destination `(pd, cd)` reused, or fresh) is a live local -/
theorem LN.of_res {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {pd cd : Nat} (hd : DL R L st zp zc M L1 pd cd) (hLL : ∀ r ∈ L, r ∈ L1)
    (hok : StkOK M R L1 st) (hc0 : stCap M st = 0 → stW M st = 0)
    {need p' l' c' v : Nat} (hr : ExpHyp.NatOF R L1 L2 M' pd cd need p' l' c' v) (hx : LiveExt R L1 L2)
    (hsb : StackBackL R L1 L2 st M M') (hrs : ¬ (p' = pd ∧ c' = cd) → ResSep M M' st p' c') (h0 : c' = 0 → p' = 0) :
    LN R L st zp zc M' L2 p' l' c' v := by
  obtain ⟨hv, hn, hlc, hc40, hlv, hof⟩ := hr
  refine ⟨⟨hc40, hlv, ?_, fun hc => ?_, h0⟩, hlc, hv, hn⟩
  · rcases hof with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
    · exact hd.2.2.1
    · exact Or.inr (Or.inl ⟨hin, fun r hr => hap r (hLL r hr)⟩)
  · by_cases ho : p' = pd ∧ c' = cd
    · obtain ⟨rfl, rfl⟩ := ho
      exact (hd.2.2.2.1 hc).back hx hsb.1
    · obtain ⟨-, hin, hap⟩ := hof.resolve_left ho
      exact ob_fresh (L := L) hok hc0 hsb.1 hin hap (hlv hc).2.1 (hrs ho) hc

/-- the result is `Pw`-apart from every non-empty live buffer other than the destination -/
theorem pw_res {R : RtInv} {L L1 L2 : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {pd cd p' c' q k : Nat}
    {need l' v : Nat} (hr : ExpHyp.NatOF R L1 L2 M' pd cd need p' l' c' v) (hq : DL R L st zp zc M L1 q k)
    (hpq : Pw pd cd q k) : Pw p' c' q k := by
  obtain ⟨-, -, -, -, -, hof⟩ := hr
  rcases hof with ⟨rfl, rfl⟩ | ⟨-, hin, hap⟩
  · exact hpq
  · intro _ hk
    exact hfresh (hq.2.1 hk).2.1 hap hin

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- **the generic callee step** with two destinations (see the module doc) -/
theorem stepC2 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd pe ce : Nat}
    (hd : Loc R L zp zc pd cd) (he : Loc R L zp zc pe ce)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 120)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++
      [(pd, pd + 8 * cd), (pe, pe + 8 * ce)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd), (pe, pe + 8 * ce)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    WC R L K g sp st zp zc s.mem M' L2 b2 ℓ ∧
    (∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 120 ≤ a ∧ a + k ≤ sp + 544) → M'.readLE a k = M.readLE a k) ∧
    (∀ q l c v, LN R L st zp zc M L1 q l c v → Pw q c pd cd → Pw q c pe ce → LN R L st zp zc M' L2 q l c v) ∧
    (∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L2 q c) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hdw := Loc.win hP hd
  have hew := Loc.win hP he
  unfold Apart at hdw hew
  have hzs : ∀ a k, sp - K ≤ a → a + k ≤ sp + 544 → Outside a k [(pd, pd + 8 * cd), (pe, pe + 8 * ce)] := by
    intro a k h1 h2
    simp only [outside_cons, outside_nil, and_true]
    omega
  have hk := keepC hP h hF hstk habove hzs
  have hw : WC R L K g sp st zp zc s.mem M' L2 b2 ℓ := by
    refine h.call (ws := [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd), (pe, pe + 8 * ce)] ++
      stkWs M st) (by simpa only [List.append_assoc] using hF) hLF hrg ?_ ?_ hx hinv
      hsb.1.1 (hsb.1.2.1.trans h.len) (Nat.le_refl _) hsb.1.2.2 hsb.2
    · intro a k o1 o2 o3 o4
      have s1 := Loc.sub (st := st) (m0 := s.mem) hd a k o1 o4
      have s2 := Loc.sub (st := st) (m0 := s.mem) he a k o1 o4
      simp only [outside_cons, outside_nil, and_true] at s1 s2
      rw [outside_append, outside_append]
      refine ⟨⟨?_, by simp only [outside_cons, outside_nil, and_true]; exact ⟨s1, s2⟩⟩, o3⟩
      simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢; omega
    · intro a k hin ho
      have s1 := Loc.subL (st := st) (m0 := s.mem) hd a k hin ho
      have s2 := Loc.subL (st := st) (m0 := s.mem) he a k hin ho
      simp only [outside_cons, outside_nil, and_true] at s1 s2
      rw [outside_append]
      exact ⟨by simp only [outside_cons, outside_nil, and_true]; exact ⟨s1, s2⟩, stk_out h (Or.inl hin) ho⟩
  refine ⟨hw, hk, fun q l c v hq hqd hqe => hq.keep hx hF.accessible hsb.1 (fun c0 a k h1 h2 => ?_),
    fun q c hq => hq.back hx hF.accessible hsb.1⟩
  obtain ⟨w1, w2, -, -⟩ := Loc.ap hP hq.1.2.2.1 c0
  have hob := hq.1.2.2.2.1 c0
  have hout := hob.out (h.sok.2.2.2.2.2.1) w2
  unfold Apart at w1
  simp only [stkWs, outside_cons, outside_nil, and_true] at hout
  have hdq : ∀ i, a ≤ i → i < a + k → i + 1 ≤ pd ∨ pd + 8 * cd ≤ i := by
    intro i hi1 hi2
    rcases Nat.eq_zero_or_pos cd with d0 | d0
    · omega
    · have := hqd c0 d0; unfold Apart at this; omega
  have heq : ∀ i, a ≤ i → i < a + k → i + 1 ≤ pe ∨ pe + 8 * ce ≤ i := by
    intro i hi1 hi2
    rcases Nat.eq_zero_or_pos ce with d0 | d0
    · omega
    · have := hqe c0 d0; unfold Apart at this; omega
  apply Memory.readLE_congr
  intro i hi
  have := keepH (cw := [(sp - stk, sp - 8), (sp + 8, sp + above)]) (a := a + i) (k := 1) hF hLF
    (hob.1.sub (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]
        exact ⟨hdq (a + i) (by omega) (by omega), heq (a + i) (by omega) (by omega)⟩)
    (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega)
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

set_option maxRecDepth 20000 in
/-- `stepC2` with one destination -/
theorem stepC1 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    (hd : Loc R L zp zc pd cd) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 120)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    WC R L K g sp st zp zc s.mem M' L2 b2 ℓ ∧
    (∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 120 ≤ a ∧ a + k ≤ sp + 544) → M'.readLE a k = M.readLE a k) ∧
    (∀ q l c v, LN R L st zp zc M L1 q l c v → Pw q c pd cd → LN R L st zp zc M' L2 q l c v) ∧
    (∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L2 q c) := by
  have hF2 : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++
      [(pd, pd + 8 * cd), (pd, pd + 8 * cd)] ++ stkWs M st) := hF.mono fun a k ho => by
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨ho.1.1, ho.1.2.1⟩, ho.2⟩
  have hL2 : LiveFrame M M' L1 ([(pd, pd + 8 * cd), (pd, pd + 8 * cd)] ++ stkWs M st) :=
    Expmc.liveFrame_widen hLF fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨ho.1.1, ho.2⟩
  obtain ⟨h1, h2, h3, h4⟩ := stepC2 hP h hd hd hstk habove hF2 hL2 hrg hx hinv hsb
  exact ⟨h1, h2, fun q l c v hq hqd => h3 q l c v hq hqd hqd, h4⟩

end

end FvModexp.Arm64.ExpSlow
