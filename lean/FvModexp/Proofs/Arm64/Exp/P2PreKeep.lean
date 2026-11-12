import FvModexp.Proofs.Arm64.Exp.P2PreDefs

/-!
# `buildPrecomputationWindowModPower2` (arm64): `Ctx` through a callee (agent infra)

Byte-wise frame reads (`frame_read`, `lf_read`: degenerate ranges `[lo, lo)` of a frame list never matter), the ranges a
callee may write besides runtime memory and its window (`WOK`: inside the entry stack object's free part or header, or a
runtime block apart from `L`), and `keepC`: the context `Ctx` after a callee whose frame is
`R.rt ++ winA S' kC aC ++ ws` with `ws` all `WOK`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

theorem outside_of_forall {b k : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, b + k ≤ r.1 ∨ r.2 ≤ b) → Outside b k rs
  | [], _ => trivial
  | (lo, hi) :: rs, h => ⟨h (lo, hi) List.mem_cons_self, outside_of_forall fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem byte_out {rs : List (Nat × Nat)} {a n i : Nat} (hi : i < n)
    (ho : ∀ r ∈ rs, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a) : Outside (a + i) 1 rs :=
  outside_of_forall fun r hr => by
    by_cases h : r.1 < r.2
    · have := ho r hr h; omega
    · omega

/-- a frame read where only the non-empty ranges of the frame list must be apart -/
theorem frame_read {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a n : Nat}
    (ho : ∀ r ∈ rs, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a) : m'.readLE a n = m.readLE a n :=
  Memory.readLE_congr fun i hi => by
    have := h.readLE (a + i) 1 (byte_out hi ho)
    simp only [Memory.readLE_one] at this
    exact BitVec.eq_of_toNat_eq this

theorem lf_read {m m' : Memory} {L ws : List (Nat × Nat)} (h : LiveFrame m m' L ws) {a n : Nat}
    (hin : InRanges a n L) (ho : ∀ r ∈ ws, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a) : m'.readLE a n = m.readLE a n :=
  Memory.readLE_congr fun i hi => by
    have := h.readLE (a + i) 1 (hin.sub (by omega) (by omega)) (byte_out hi ho)
    simp only [Memory.readLE_one] at this
    exact BitVec.eq_of_toNat_eq this

/-- a range a callee may write (besides `R.rt` and its window): non-empty ⇒ in the entry stack object's free part
or header, or a runtime block apart from `L` -/
@[reducible] def WOK (R : RtInv) (L : List (Nat × Nat)) (s : State) (st : Nat) (r : Nat × Nat) : Prop :=
  r.1 < r.2 → (stW s.mem st + 8 * stLen s.mem st ≤ r.1 ∧ r.2 ≤ stW s.mem st + 8 * stCap s.mem st) ∨
    (st ≤ r.1 ∧ r.2 ≤ st + 24) ∨ (InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L)

theorem in_rt_sep {rt : List (Nat × Nat)} {a n lo hi : Nat} (h : InRanges lo (hi - lo) rt) (ho : Outside a n rt)
    (hlh : lo < hi) : a + n ≤ lo ∨ hi ≤ a := by
  have := h.apart ho; unfold Apart at this; omega

/-- a `WOK` range is apart from everything outside `AW` -/
theorem wok_aw {R : RtInv} {L : List (Nat × Nat)} {s : State} {kc pw pl st : Nat} {r : Nat × Nat}
    (h : WOK R L s st r) {a n : Nat} (ho : Outside a n (AW R kc s pw pl st)) (hr : r.1 < r.2) :
    a + n ≤ r.1 ∨ r.2 ≤ a := by
  rw [AW, outside_append, outside_append] at ho
  obtain ⟨⟨hrt, -⟩, ho⟩ := ho
  simp only [LW, stWs, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
  rcases h hr with h | h | ⟨h, -⟩
  · omega
  · omega
  · exact in_rt_sep h hrt hr

/-- a `WOK` range is apart from every object of `L` outside `LW` -/
theorem wok_L {R : RtInv} {L : List (Nat × Nat)} {s : State} {pw pl st : Nat} {r : Nat × Nat}
    (h : WOK R L s st r) {a n : Nat} (hin : InRanges a n L) (ho : Outside a n (LW s pw pl st)) (hr : r.1 < r.2) :
    a + n ≤ r.1 ∨ r.2 ≤ a := by
  simp only [LW, stWs, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
  rcases h hr with h | h | ⟨-, h⟩
  · omega
  · omega
  · have := h.apart_of_inRanges hin; unfold Apart at this; omega

/-- the window facts a `WOK` range needs to be apart from the window -/
structure WinF (R : RtInv) (kc : Nat) (s : State) (st : Nat) : Prop where
  rt : Outside (s.sp.toNat - K kc) (K kc + A) R.rt
  hd : Outside st 24 (win s (K kc) A)
  ar : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s (K kc) A)
  sp : K kc ≤ s.sp.toNat
  kc8 : 8 ≤ kc

theorem wok_win {R : RtInv} {L : List (Nat × Nat)} {s : State} {kc st : Nat} {r : Nat × Nat}
    (h : WOK R L s st r) (hw : WinF R kc s st) (hr : r.1 < r.2) :
    s.sp.toNat + A ≤ r.1 ∨ r.2 ≤ s.sp.toNat - K kc := by
  have h1 := hw.hd
  simp only [win, outside_cons, outside_nil, and_true] at h1
  rcases h hr with h | h | ⟨h, -⟩
  · have h2 := hw.ar (by omega)
    simp only [win, outside_cons, outside_nil, and_true] at h2
    omega
  · omega
  · have := in_rt_sep h hw.rt hr; omega

theorem wok_buf {R : RtInv} {L L1 : List (Nat × Nat)} {s : State} {M : Memory} {st bp k zp zn : Nat}
    (h : Scr R L L1 s.mem M st bp k) (h1 : bp ≤ zp) (h2 : zp + zn ≤ bp + 8 * k) : WOK R L s st (zp, zp + zn) := by
  intro hr
  simp only at hr ⊢
  rcases h.loc with ⟨-, a1, a2⟩ | ⟨a1, a2⟩
  · left; omega
  · right; right; exact ⟨a1.sub (by omega) (by omega), ApartAll.sub' a2 (by omega) (by omega)⟩

theorem wok_stk {R : RtInv} {L L1 : List (Nat × Nat)} {s : State} {M : Memory} {st pl lm : Nat}
    (h : StkAfter R L L1 st (stLen s.mem st) pl lm s.mem M) : ∀ r ∈ stWs M st, WOK R L s st r := by
  intro r hr
  simp only [stWs, stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, hl, ha⟩ := h
  rcases hr with rfl | rfl
  · intro _; right; left; simp only; omega
  · intro hr
    simp only at hr ⊢
    rcases ha with ⟨e1, e2⟩ | ⟨a1, a2⟩
    · left; rw [e1, e2] at hr ⊢; rw [hl]; omega
    · right; right; exact ⟨a1.sub (by omega) (by omega), ApartAll.sub' a2 (by omega) (by omega)⟩

set_option maxRecDepth 20000 in
/-- the slots are kept by a callee at `S'` (`SP' = SP - 208`) writing its window and `WOK` ranges -/
theorem sl_keep {R : RtInv} {L L1 : List (Nat × Nat)} {s S' : State} {kc st pw pl lm : Nat} {M M' : Memory}
    (hw : WinF R kc s st) (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws))
    (h : Sl s st pw pl lm M) : Sl s st pw pl lm M' := by
  have hK := hw.sp
  have hrt := hw.rt
  have hk8 := hw.kc8
  simp only [K, A] at hK hrt
  have key : ∀ a, s.sp.toNat - 216 ≤ a → a + 8 ≤ s.sp.toNat + 80 → (a + 8 ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 120 ≤ a) →
      M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    refine frame_read hF fun ⟨r1, r2⟩ hr hr' => ?_
    show a + 8 ≤ r1 ∨ r2 ≤ a
    simp only [List.mem_append, winA, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr hr'
    rcases hr with (hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hr
    · have := MemFrame.outside_mem (hrt.of_sub (a := a) (n := 8) (by omega) (by omega)) hr
      simp only at this; omega
    · omega
    · omega
    · have := wok_win (hws _ hr) hw hr'; simp only [K, A] at this; omega
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := h
  exact ⟨(key _ (by omega) (by omega) (by omega)).trans e0, (key _ (by omega) (by omega) (by omega)).trans e1,
    (key _ (by omega) (by omega) (by omega)).trans e2, (key _ (by omega) (by omega) (by omega)).trans e3,
    (key _ (by omega) (by omega) (by omega)).trans e4, (key _ (by omega) (by omega) (by omega)).trans e5,
    (key _ (by omega) (by omega) (by omega)).trans e6, (key _ (by omega) (by omega) (by omega)).trans e7,
    (key _ (by omega) (by omega) (by omega)).trans e8⟩

theorem apartAll_of_ext {R : RtInv} {L L1 : List (Nat × Nat)} (h : LiveExt R L L1) {a n : Nat}
    (ha : ApartAll a n L1) : ApartAll a n L := fun r hr => ha r (h.mem_old hr)

theorem sa_back {R : RtInv} {L L1 L2 : List (Nat × Nat)} {st ℓ pl lm : Nat} {m0 M M' : Memory}
    (h : StkAfter R L L1 st ℓ pl lm m0 M) (hb : StackBack R L1 L2 st M M') (hLE : LiveExt R L L1) :
    StkAfter R L L2 st ℓ pl lm m0 M' := by
  obtain ⟨-, hl, ha⟩ := h
  obtain ⟨hok, hl', hb⟩ := hb
  refine ⟨hok, hl'.trans hl, ?_⟩
  rcases hb with ⟨e1, e2⟩ | ⟨a1, a2⟩
  · rw [e1, e2]; exact ha
  · exact Or.inr ⟨a1, apartAll_of_ext hLE a2⟩

set_option maxRecDepth 20000 in
/-- **the context after a callee** at `S'` (`SP' = SP - 208`, window `[SP' - kC, SP' + aC)`) writing `ws` (all `WOK`) -/
theorem keepC {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm : Nat} {s : State} {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) (hw : WinF R kc s st)
    {S' : State} (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws) (hrg : M'.regions = M.regions)
    (hLE : LiveExt R L1 L2) (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M'))
    (hsa : StkAfter R L L2 st (stLen s.mem st) pl lm s.mem M') (hsap : StkApart M' st bp (8 * NB pl lm)) :
    Ctx R kc L st pw pl lm s bp M' L2 b2 := by
  have hK := hw.sp
  simp only [K] at hK
  refine ⟨⟨fun a n ho => (frame_read hF fun r hr hr' => ?_).trans (hc.fr.readLE a n ho),
      fun a n w => (hF.accessible a n w).trans (hc.fr.accessible a n w)⟩,
    ⟨fun a n hin ho => (lf_read hLF (hc.le.inRanges_old hin) fun r hr hr' => wok_L (hws r hr) hin ho hr').trans
      (hc.lf.readLE a n hin ho)⟩, hrg.trans hc.rg, hc.le.trans hLE, hinv,
    ⟨hc.scr.b48, by rw [hF.accessible]; exact hc.scr.acc, hc.scr.al, hLE.held hc.scr.held, hc.scr.loc⟩, hsa, hsap,
    sl_keep (L1 := L1) hw hsp hk ha hws hF hc.sl⟩
  have ho' := ho
  rw [AW, outside_append, outside_append] at ho'
  obtain ⟨⟨hrt, hwa⟩, -⟩ := ho'
  simp only [winA, K, A, outside_cons, outside_nil, and_true] at hwa
  simp only [List.mem_append, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (hr | hr | hr) | hr
  · have := MemFrame.outside_mem hrt hr; omega
  · subst hr; simp only at hr' ⊢; omega
  · subst hr; simp only at hr' ⊢; omega
  · exact wok_aw (hws r hr) ho hr'

/-- the buffer stays apart from the stack's header and free part through a callee that restores the stack -/
theorem sap_back {R : RtInv} {L1 L2 : List (Nat × Nat)} {st bp n : Nat} {M M' : Memory}
    (h : StkApart M st bp n) (hh : Held R L1 bp n) (hb : StackBack R L1 L2 st M M') : StkApart M' st bp n := by
  obtain ⟨-, hl, hb⟩ := hb
  intro hn
  refine ⟨(h hn).1, fun hlt => ?_⟩
  rcases hb with ⟨e1, e2⟩ | ⟨a1, a2⟩
  · simp only [stLen, stW, stCap] at e1 e2 hl hlt h ⊢
    rw [e2, hl] at hlt; rw [e1, e2, hl]
    exact (h hn).2 hlt
  · rcases hh with hL | hO
    · have := a2.apart_of_inRanges hL; unfold Apart at this ⊢; omega
    · have := a1.apart hO; unfold Apart at this ⊢; omega

/-- a held range outside the function's window is kept by a callee (frame `R.rt ++ winA S' kC aC ++ ws`) if it is
apart from every non-empty range of `ws` -/
theorem rd_keep {R : RtInv} {kc : Nat} {s S' : State} {st : Nat} (hw : WinF R kc s st)
    (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {L1 ws : List (Nat × Nat)} {M M' : Memory} (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws))
    (hLF : LiveFrame M M' L1 ws) {a n : Nat} (hh : Held R L1 a n)
    (hwin : s.sp.toNat + A ≤ a ∨ a + n ≤ s.sp.toNat - K kc)
    (hws : ∀ r ∈ ws, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a) : M'.readLE a n = M.readLE a n := by
  have hK := hw.sp
  simp only [K, A] at hK hwin
  rcases hh with hL | hO
  · exact lf_read hLF hL hws
  · refine frame_read hF fun r hr hr' => ?_
    simp only [List.mem_append, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (hr | hr | hr) | hr
    · have := MemFrame.outside_mem hO hr; omega
    · subst hr; simp only at hr' ⊢; omega
    · subst hr; simp only at hr' ⊢; omega
    · exact hws r hr hr'

/-- the non-empty ranges of a `sqr` / `mul` frame `[z] ++ stWs M st` are apart from a buffer range apart from `z` -/
theorem ws_apart {M : Memory} {st bp k zp zn a n : Nat} (hsap : StkApart M st bp k) (h1 : bp ≤ a)
    (h2 : a + n ≤ bp + k) (h0 : 0 < n) (hz : Apart a n zp zn) :
    ∀ r ∈ [(zp, zp + zn)] ++ stWs M st, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a := by
  intro r hr hr'
  simp only [stWs, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hs := hsap (by omega)
  unfold Apart at hz hs
  rcases hr with rfl | rfl | rfl <;> simp only at hr' ⊢
  · omega
  · omega
  · have := hs.2 (by omega); unfold Apart at this; omega

end FvModexp.Arm64.P2Pre
