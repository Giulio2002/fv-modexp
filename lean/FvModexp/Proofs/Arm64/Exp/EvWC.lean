import FvModexp.Proofs.Arm64.Exp.EvCtx

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64; copy of `P2W2WC`): the shared context `WC` of every point after the entry (agent infra)

`WC R L K g sp st zp zc m0 M L1 b1 ℓ`: the memory `M` at a point of the function (entry memory `m0`, entry live set
`L`) differs from `m0` only in the runtime ranges, the function's window `WN` (`[sp - K, sp + 448)` without the
caller's saved FP/LR `[sp + 328, sp + 344)`) and `ZS` (`z`'s array, the stack header, the entry free part of the
stack's array); live objects of `L` keep their bytes outside `ZS`; the live set `L1` extends `L`, the invariant holds
with budget `b1`; the stack is `StkOK` at level `ℓ ≥ ℓ₀` with its array the entry one or fresh (relative to `L`) and,
when fresh, an element of `L1` (`ArrIn`, for the final `StackBackL`).

This is the module every later segment imports (ROW-TIME rule); transport lemmas: `WC.frame` (own writes / a callee
that keeps the stack), `WC.call` (a callee post with a new live set and stack level), `WC.stkNat` (`(*stack).nat`'s
`PostL`); read lemmas `WC.read`, `stk_out`, `free_apart`; `Scr.rebase` (a callee's scratch nat relative to the entry).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the window ranges the function writes (entry `SP = sp + 336`) -/
@[reducible] def WN (sp K : Nat) : List (Nat × Nat) := [(sp - K, sp + 328), (sp + 344, sp + 448)]

/-- the caller-visible ranges the function writes: `z`'s array, the stack header and the entry free part -/
@[reducible] def ZS (zp zc st : Nat) (m0 : Memory) : List (Nat × Nat) := [(zp, zp + 8 * zc)] ++ stkWs m0 st

/-- the context at every point after the entry (see the module doc) -/
structure WC (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory) (L1 : List (Nat × Nat))
    (b1 ℓ : Nat) : Prop where
  fr : MemFrame m0 M (R.rt ++ WN sp K ++ ZS zp zc st m0)
  lf : LiveFrame m0 M L (ZS zp zc st m0)
  rg : M.regions = m0.regions
  le : LiveExt R L L1
  inv : R.inv b1 L1 g (view R.rt L1 M)
  sok : StkOK M R L1 st
  len : stLen M st = ℓ
  lo : stLen m0 st ≤ ℓ
  lc0 : stLen m0 st ≤ stCap m0 st
  kf : ArrKF R L st m0 M
  ain : ArrIn L1 st m0 M

/-- a read whose every byte is outside the frame's ranges -/
theorem MemFrame.bytewise {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a n : Nat}
    (hb : ∀ i, i < n → Outside (a + i) 1 rs) : m'.readLE a n = m.readLE a n := by
  apply Memory.readLE_congr
  intro i hi
  have := h.readLE (a + i) 1 (hb i hi)
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

section
variable {R : RtInv} {L : List (Nat × Nat)} {K g sp st zp zc : Nat} {m0 M : Memory} {L1 : List (Nat × Nat)}
    {b1 ℓ : Nat}

/-- a held range (live in `L` or outside the runtime) outside the entry free part is apart from the free part now -/
theorem free_apart (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hf : Apart a k (free m0 st).1 (free m0 st).2) : Apart a k (free M st).1 (free M st).2 := by
  have hc := h.sok.2.2.2.2.2.1
  have hl := h.len
  have hlo := h.lo
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    simp only [Apart] at hf ⊢; rw [e1, e2]; omega
  · have : a + k ≤ stW M st ∨ stW M st + 8 * stCap M st ≤ a := by
      rcases hh with hL | hO
      · have := hap.apart_of_inRanges hL; omega
      · have := hin.apart hO; unfold Apart at this; omega
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    unfold Apart; omega

/-- a held range outside `ZS` is outside the stack's writable ranges now -/
theorem stk_out (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (ho : Outside a k (ZS zp zc st m0)) : Outside a k (stkWs M st) := by
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
  refine ⟨ho.2.1, ?_⟩
  have := h.lc0
  have := free_apart h hh (by simp only [Apart]; omega)
  simp only [Apart] at this
  have hc := h.sok.2.2.2.2.2.1
  omega

/-- the read form: a held range outside the window and `ZS` keeps its bytes -/
theorem WC.read (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hw : Outside a k (WN sp K)) (ho : Outside a k (ZS zp zc st m0)) : M.readLE a k = m0.readLE a k :=
  Expmc.held_readLE hh h.fr h.lf hw ho

/-- a range outside everything the function may write is outside the runtime and the stack's writable ranges now -/
theorem out_all (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat}
    (ho : Outside a k (R.rt ++ WN sp K ++ ZS zp zc st m0)) :
    Outside a k R.rt ∧ Outside a k (WN sp K) ∧ Outside a k (stkWs M st) := by
  rw [outside_append, outside_append] at ho
  exact ⟨ho.1.1, ho.1.2, stk_out h (Or.inr ho.1.1) ho.2⟩

/-- `WC` through a step that writes `ws` and keeps the stack header (the function's own stores, a callee that
does not change the stack object) -/
theorem WC.frame (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {M' : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hsub : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st m0) → Outside a k ws)
    (hL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st m0) → Outside a k ws)
    (hhd : Outside st 24 ws) (hws : ∀ r ∈ ws, InRanges r.1 (r.2 - r.1) L1 ∨ Outside r.1 (r.2 - r.1) R.rt) :
    WC R L K g sp st zp zc m0 M' L1 b1 ℓ := by
  have e0 : stW M' st = stW M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M' st = stLen M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M' st = stCap M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  refine ⟨h.fr.trans hF fun a k ho => ⟨ho, hsub a k ho⟩,
    ⟨fun a k hin ho => by rw [hF.readLE a k (hL a k hin ho), h.lf.readLE a k hin ho]⟩, hrg.trans h.rg, h.le,
    Expmc.inv_frame hF hws h.inv, stkOK_hdr h.sok hF e0 e1 e2 (LiveExt.refl R L1), by rw [e1]; exact h.len, h.lo, h.lc0,
    ?_, ?_⟩
  · rcases h.kf with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨e0.trans a1, e2.trans a2⟩
    · exact Or.inr (by rw [e0, e2]; exact ⟨a1, a2⟩)
  · exact h.ain.congr e0 e2 fun _ hr => hr

/-- `WC` through a callee whose post has a new live set `L2`, budget `b2` and stack level `ℓ'` (array kept, or
fresh relative to `L1` and then an element of `L2`) -/
theorem WC.call (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {M' : Memory} {ws ws' : List (Nat × Nat)}
    {L2 : List (Nat × Nat)} {b2 ℓ' : Nat}
    (hF : MemFrame M M' (R.rt ++ ws)) (hLF : LiveFrame M M' L1 ws') (hrg : M'.regions = M.regions)
    (hsub : ∀ a k, Outside a k R.rt → Outside a k (WN sp K) → Outside a k (stkWs M st) →
      Outside a k (ZS zp zc st m0) → Outside a k ws)
    (hL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st m0) → Outside a k ws')
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hok : StkOK M' R L2 st)
    (hlen : stLen M' st = ℓ') (hle : ℓ ≤ ℓ')
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1))
    (hmem : ArrIn L2 st M M') :
    WC R L K g sp st zp zc m0 M' L2 b2 ℓ' := by
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => h.le.mem_old hr
  refine ⟨h.fr.trans hF fun a k ho => ⟨ho, ?_⟩, ⟨fun a k hin ho => ?_⟩, hrg.trans h.rg, h.le.trans hx, hinv, hok,
    hlen, by have := h.lo; omega, h.lc0, ?_, h.ain.trans hmem hx⟩
  · obtain ⟨o1, o2, o3⟩ := out_all h ho
    rw [outside_append, outside_append] at ho
    rw [outside_append]
    exact ⟨o1, hsub a k o1 o2 o3 ho.2⟩
  · rw [hLF.readLE a k (h.le.inRanges_old hin) (hL a k hin ho), h.lf.readLE a k hin ho]
  · rcases harr with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rcases h.kf with ⟨b1', b2'⟩ | ⟨b1', b2'⟩
      · exact Or.inl ⟨a1.trans b1', a2.trans b2'⟩
      · exact Or.inr (by rw [a1, a2]; exact ⟨b1', b2'⟩)
    · exact Or.inr ⟨a1, fun r hr => a2 r (hLL r hr)⟩

/-- a scratch nat of a callee (relative to the call memory `M`) is one relative to the entry -/
theorem Scr.rebase (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {L2 : List (Nat × Nat)} {M' : Memory} {t k : Nat}
    (hs : Scr R L1 L2 M M' st t k) : Scr R L L2 m0 M' st t k := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  refine ⟨s1, s2, s3, s4, ?_⟩
  have hl := h.len
  have hlo := h.lo
  rcases s5 with ⟨c0, c1, c2⟩ | ⟨c1, c2⟩
  · rcases h.kf with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · left; rw [← e1, ← e2]; exact ⟨c0, by omega, c2⟩
    · right; exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
  · right; exact ⟨c1, fun r hr => c2 r (h.le.mem_old hr)⟩

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

theorem EPre.win_rt (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) : Outside (sp - K) (K + 448) R.rt := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have := hP.1.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.mem_singleton_self _)
  simp only at this; rwa [show sp + 448 - (sp - K) = K + 448 by omega] at this

theorem EPre.stk0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) : StkOK s.mem R L st :=
  hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- every range the function writes (besides the runtime's) is writable at the entry -/
theorem EPre.ws_acc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) :
    ∀ r ∈ WN sp K ++ ZS zp zc st s.mem, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hacc, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz,
    -, ⟨-, -, k3, -, k5, -, -⟩, -⟩ := hP
  intro r hr hlt
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only at hlt ⊢
  · exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact (hz (by omega)).2.1
  · rw [show st + 24 - st = 24 by omega]; exact k3
  · exact Memory.accessible_mono _ (k5 (by omega)).2.2.1 (by omega) (by omega)

/-- the guard word's bytes are outside every range the function writes (byte-wise: `z`'s array and the free part
may be empty ranges anywhere) -/
theorem EPre.g_out (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) :
    ∀ i, i < 8 → Outside (g + 16 + i) 1 (R.rt ++ WN sp K ++ ZS zp zc st s.mem) := by
  obtain ⟨⟨-, -, -, -, -, hgo, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz,
    -, ⟨-, -, -, -, -, hlc, -⟩, -, hstg, harr, -⟩ := hP
  intro i hi
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
    and_true] at hgo ⊢
  unfold Apart at hstg
  refine ⟨⟨hgo.2.of_sub (by omega) (by omega), by omega, by omega⟩, ?_, by omega, ?_⟩
  · rcases Nat.eq_zero_or_pos zc with h0 | h0
    · subst h0; omega
    · have := (hz h0).2.2.2.2.1; unfold Apart at this; omega
  · rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · omega
    · have := (harr h0).2; unfold Apart at this; omega

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- the callee environment at `SP = sp` -/
theorem WC.cenv (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) : CallW.CEnv R L1 g sp K 88 M := by
  have hgM : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := MemFrame.bytewise h.fr hP.g_out
  have hws := hP.ws_acc
  have hout := hP.win_rt
  obtain ⟨⟨-, -, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc0, -, hLs, hd, -⟩, -, -, hro, -⟩ := hP
  simp only [outside_cons] at hgo
  refine ⟨hal, by omega, by omega, by rw [h.fr.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega),
    hg1, by rw [h.fr.accessible]; exact hg2, by rw [hgM]; omega, hout.of_sub (by omega) (by omega),
    by unfold Apart; omega, hgo.2, ?_, dataLoaded_frame hd h.rg hro (by rw [← List.append_assoc]; exact h.fr) hws, hro⟩
  refine h.le.liveSep (LiveSep.sub_win hLs (by omega) (by omega)) fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr; simp only
  exact hout.of_sub (by omega) (by omega)

end

/-- a held range (adapted from `ModInv.held_bytes`): every byte outside the extra ranges keeps its value -/
theorem held_bytesW {rt L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (hh : InRanges a n L ∨ Outside a n rt) (hf : MemFrame m m' (rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (h : ∀ i, i < n → Outside (a + i) 1 ws1 ∧ Outside (a + i) 1 ws2) : m'.readLE a n = m.readLE a n := by
  apply Memory.readLE_congr
  intro i hi
  have hh1 : InRanges (a + i) 1 L ∨ Outside (a + i) 1 rt :=
    hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have := Expmc.held_readLE hh1 hf hl (h i hi).1 (h i hi).2
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- byte-wise read through `WC` -/
theorem WC.readB (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hb : ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st s.mem)) :
    M.readLE a k = s.mem.readLE a k :=
  held_bytesW hh h.fr h.lf hb

/-- the bytes of an entry object (`OE`, apart from `z` when `z` is not empty) are outside the function's writes -/
theorem oe_bytes (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {a k : Nat} (hoe : OE R L sp K st s.mem a k)
    (hza : 0 < zc → Apart zp (8 * zc) a k) :
    ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st s.mem) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨-, h2, h3, h4⟩ := hoe
  intro i hi
  simp only [Apart] at h2 h3 h4
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨by omega, by omega⟩, ?_, by omega, by omega⟩
  rcases Nat.eq_zero_or_pos zc with h0 | h0
  · subst h0; omega
  · have := hza h0; unfold Apart at this; omega

/-- the stack's array apart from a window range (`Outside` the runtime) whenever its free part is not empty -/
theorem free_apart' (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {a k : Nat} (hrt : Outside a k R.rt)
    (hf : 0 < stCap s.mem st → Apart a k (stW s.mem st) (8 * stCap s.mem st)) :
    stLen M st < stCap M st → Apart a k (free M st).1 (free M st).2 := by
  intro hlt
  have hl := h.len
  have hlo := h.lo
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · have := hf (by rw [← e2]; omega)
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    simp only [Apart] at this ⊢; rw [e1, e2]; rw [e2] at hlt; omega
  · have := hin.apart hrt
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    unfold Apart at this ⊢; omega

/-- the stack object as a callee at `SP = sp` needs it -/
theorem WC.stkIn (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {S' : State} (hsp : S'.sp.toNat = sp) (h28 : (S'.regs 28).toNat = g) (hm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 88) : EvenHyp.StkIn R L1 S' stk above st := by
  have hout := hP.win_rt
  obtain ⟨⟨-, -, -, -, -, hgo, -, -, hK, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hstw, hstg, harr, -⟩ := hP
  simp only [outside_cons] at hgo
  unfold Apart at hstw
  subst hm
  refine ⟨h.sok, ?_, by rw [h28]; exact hstg, fun hc0 => ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rw [h28]
    rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc0; rw [e1, e2]
      obtain ⟨o1, o2⟩ := harr hc0
      unfold Apart at o1
      refine ⟨?_, o2⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
    · have a1 := hin.apart hout
      have a2 := hin.apart hgo.2
      unfold Apart at a1 a2 ⊢
      refine ⟨?_, by omega⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

set_option maxRecDepth 20000 in
/-- the globals at `M`, outside any window `w` inside `[sp - K, sp + 448)` and the header -/
theorem WC.globals (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {w : List (Nat × Nat)} (hw : ∀ a n, Outside a n [(sp - K, sp + 448), (st, st + 24)] → Outside a n w) :
    RunIface.Globals R M w := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hzA : 0 < zc → Apart zp (8 * zc) RunIface.gA 32 := fun h0 => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).2.2.2.2.2.2.2
  have hb := oe_bytes hP hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hzA
  obtain ⟨-, -, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, ⟨-, -, hgst, -⟩, -, -, -, -, -, hwbA, -⟩ := hP
  have hrd : ∀ j, j + 8 ≤ 32 → M.readLE (RunIface.gA + j) 8 = s.mem.readLE (RunIface.gA + j) 8 := fun j hj =>
    h.readB (Or.inr (g9.of_sub (by omega) (by omega))) fun i hi => by
      have := hb (j + i) (by omega); rwa [← Nat.add_assoc] at this
  simp only [outside_cons, outside_nil, and_true] at g10 g13
  have ewb : StackNat.wbA = RunIface.wbA := by decide
  rw [ewb] at hwbA
  unfold Apart at hgst hwbA
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [h.fr.accessible]; exact g8, g9,
    hw _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
    by rw [h.fr.accessible]; exact g11, g12, hw _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
  · rw [g5, hrd 8 (by omega), ← g5]; exact g1
  · rw [g6, hrd 16 (by omega), ← g6]; exact g2
  · rw [g7, hrd 24 (by omega), ← g7]; exact g3
  · have e : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
        RunIface.gA + 0 := by decide
    rw [e, hrd 0 (by omega)]; rw [← e]; exact g4

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the window is outside the runtime ranges and the stack's writable ranges (non-empty stack) -/
theorem WC.win_out (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hl : 0 < ℓ) : ∀ a k, sp - K ≤ a → a + k ≤ sp + 448 → Outside a k (R.rt ++ stkWs M st) := by
  have hout := hP.win_rt
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have harr := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlc := h.sok.2.2.2.2.2.1
  have hlen := h.len
  intro a k h1 h2
  rw [outside_append]
  refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
  simp only [stkWs, outside_cons, outside_nil, and_true]
  unfold Apart at hstw
  refine ⟨by omega, ?_⟩
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · have := (harr (by rw [← e2]; omega)).1
    rw [← e1, ← e2] at this; unfold Apart at this; omega
  · have := hin.apart (hout.of_sub (a := a) (n := k) (by omega) (by omega)); unfold Apart at this; omega

end

end FvModexp.Arm64.ExpEven
