import FvModexp.Proofs.Amd64.Exp.SlowRel
import FvModexp.Proofs.Amd64.Exp.ExpHyp

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the local buffers `z`, `zz`, `r`, `q` and the generic callee step (agent expmc s79;
port of arm64 SlowRel's `FA`/`Ob` + arm64 `SlowLN` onto the amd64 slow frame)

Every local nat of `nat.expNNSlow` is one of four buffers (nat.go:742-781); none is stack scratch. A buffer `(p, c)`
is `Loc` (the entry `z` array, FRESH relative to the entry live set `L`, or `nil`), `DL` (a destination: `c < 2^40`,
`NatLive`, `Loc`, `Ob`, `nil` when empty), `LN` (`DL` + length, value, normalisation); `Pw` = apart when both
non-empty. `stepC2`/`stepC1`: the context `WC`, the slots `[sp + 0x68, sp + 0x220)` and every `LN`/`DL` apart
from the destinations survive a callee at `RSP = sp - 8` (window `[sp - 8 - stk, sp - 8 + above)`, `above ≤ 0x70`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- a nat array the function keeps using (see the module doc): held, apart from the stack's CURRENT free part (the
entry `z` array may lie anywhere outside the entry free part, so infra's "inside the used part or apart from the whole
array" form is not available for it), and apart from the CURRENT array whenever that is fresh relative to the entry
live set `L` (`FA`; gives the final `ResSep`: a grown array is fresh, `ArrKF`) -/
@[reducible] def FA (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M : Memory) (t k : Nat) : Prop :=
  InRanges (stW M st) (8 * stCap M st) R.rt → ApartAll (stW M st) (8 * stCap M st) L →
    Apart t (8 * k) (stW M st) (8 * stCap M st)

@[reducible] def Ob (R : RtInv) (L L1 : List (Nat × Nat)) (st : Nat) (M : Memory) (t k : Nat) : Prop :=
  Held R L1 t (8 * k) ∧ Apart t (8 * k) (free M st).1 (free M st).2 ∧ FA R L st M t k

/-- `Ob` through a callee with `StackBack` (level kept; array kept, or fresh relative to `L1`) -/
theorem Ob.back {R : RtInv} {L L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : Ob R L L1 st M t k) (hx : LiveExt R L1 L2) (hsb : StackBack R L1 L2 st M M') : Ob R L L2 st M' t k := by
  refine ⟨hx.held h.1, ?_⟩
  have hl := hsb.2.1
  have hlc := hsb.1.2.2.2.2.2.1
  rcases hsb.2.2 with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · have := h.2.1
    have h3 := h.2.2
    refine ⟨?_, ?_⟩
    · show Apart t (8 * k) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
      rw [e1, e2, hl]; exact this
    · show InRanges (stW M' st) (8 * stCap M' st) R.rt → ApartAll (stW M' st) (8 * stCap M' st) L →
        Apart t (8 * k) (stW M' st) (8 * stCap M' st)
      rw [e1, e2]; exact h3
  · have hA : Apart t (8 * k) (stW M' st) (8 * stCap M' st) := (hfresh h.1 hap hin).symm
    refine ⟨?_, ?_⟩
    · show Apart t (8 * k) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
      unfold Apart at hA ⊢; omega
    · intro _ _; exact hA

/-- an `Ob` array is apart from the stack's free part -/
theorem Ob.free {R : RtInv} {L L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : Ob R L L1 st M t k) :
    Apart t (8 * k) (free M st).1 (free M st).2 := h.2.1

/-- an `Ob` array is outside the stack's writable ranges when apart from the header -/
theorem Ob.out {R : RtInv} {L L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : Ob R L L1 st M t k)
    (hlc : stLen M st ≤ stCap M st) (hst : Apart t (8 * k) st 24) : Outside t (8 * k) (stkWs M st) := by
  have := h.free
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
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- the apartness facts of a non-empty located buffer -/
theorem Loc.ap (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : Loc R L zp zc p c) (hc : 0 < c) :
    Apart p (8 * c) (sp - 8 - K) (K + 0x228) ∧ Apart p (8 * c) st 24 ∧ Apart p (8 * c) (g + 16) 8 ∧
      Apart p (8 * c) RunIface.gA 32 ∧ Apart p (8 * c) xp (8 * xl) ∧ Apart p (8 * c) yp (8 * yl) ∧
      Apart p (8 * c) mp (8 * ml) := by
  have hout := hP.win_rt
  have hsok := hP.stk0
  have hc := hP.cenv0
  obtain ⟨-, -, -, -, -, -, hoy, -, -, -, -, -, hox, -, -, -, -, -, -, -, -, hz, hogA,
    -, -, -, -, -, -, -, -, -, -, -, ⟨hom, -, -, -, hzm, -⟩, -⟩ := hP
  rcases h with ⟨rfl, rfl, hz0⟩ | ⟨hin, hap⟩ | ⟨-, rfl⟩
  · obtain ⟨⟨-, o1, o2, -⟩, -, -, -, a1, -, a2, a3, a4⟩ := hz hz0
    exact ⟨o1, o2, a1.symm, a4, a2, a3, hzm hz0⟩
  · exact ⟨(hin.apart hout).symm, hfresh hsok.2.1 hap hin, (hin.apart hc.2.2.2.2.2.2.2.2.2.1).symm,
      hfresh hogA.1 hap hin, hfresh hox.1 hap hin, hfresh hoy.1 hap hin, hfresh hom.1 hap hin⟩
  · omega

/-- a located buffer (any capacity) is apart from the window -/
theorem Loc.win (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {p c : Nat}
    (h : Loc R L zp zc p c) : Apart p (8 * c) (sp - 8 - K) (K + 0x228) := by
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
      rw [← hv]; exact Janus.Arm64.Memory.readLE_congr fun i hi => absurd hi (by omega)
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
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- **the generic callee step** with two destinations (see the module doc) -/
theorem stepC2 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd pe ce : Nat}
    (hd : Loc R L zp zc pd cd) (he : Loc R L zp zc pe ce)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x70)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++
      [(pd, pd + 8 * cd), (pe, pe + 8 * ce)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd), (pe, pe + 8 * ce)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    WC R L K g sp st zp zc s.mem M' L2 b2 ℓ ∧
    (∀ a k, sp + 0x68 ≤ a → a + k ≤ sp + 0x220 → M'.readLE a k = M.readLE a k) ∧
    (∀ q l c v, LN R L st zp zc M L1 q l c v → Pw q c pd cd → Pw q c pe ce → LN R L st zp zc M' L2 q l c v) ∧
    (∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L2 q c) := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hdw := Loc.win hP hd
  have hew := Loc.win hP he
  unfold Apart at hdw hew
  have hzs : ∀ a k, sp - 8 - K ≤ a → a + k ≤ sp + 0x220 → Outside a k [(pd, pd + 8 * cd), (pe, pe + 8 * ce)] := by
    intro a k h1 h2
    simp only [outside_cons, outside_nil, and_true]
    omega
  have hk : ∀ a k, sp + 0x68 ≤ a → a + k ≤ sp + 0x220 → M'.readLE a k = M.readLE a k :=
    fun a k h1 h2 => keepC hP h hF hstk habove hzs a k (by omega) h2
  have hw : WC R L K g sp st zp zc s.mem M' L2 b2 ℓ := by
    refine h.call (ws := [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd), (pe, pe + 8 * ce)] ++
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
  apply Janus.Arm64.Memory.readLE_congr
  intro i hi
  have := keepH (cw := [(sp - 8 - stk, sp - 8 + above)]) (a := a + i) (k := 1) hF hLF
    (hob.1.sub (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]
        exact ⟨hdq (a + i) (by omega) (by omega), heq (a + i) (by omega) (by omega)⟩)
    (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega)
  simp only [Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

set_option maxRecDepth 20000 in
/-- `stepC2` with one destination -/
theorem stepC1 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    (hd : Loc R L zp zc pd cd) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x70)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    WC R L K g sp st zp zc s.mem M' L2 b2 ℓ ∧
    (∀ a k, sp + 0x68 ≤ a → a + k ≤ sp + 0x220 → M'.readLE a k = M.readLE a k) ∧
    (∀ q l c v, LN R L st zp zc M L1 q l c v → Pw q c pd cd → LN R L st zp zc M' L2 q l c v) ∧
    (∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L2 q c) := by
  have hF2 : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++
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

end FvModexp.Amd64.ExpSlow
