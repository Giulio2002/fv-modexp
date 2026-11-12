import FvModexp.Proofs.Arm64.Exp.W4Anc

/-!
# window-4 prologue (arm64): the context without `x` (`CtxB`, before `x` is spilled) and its transfer (`KeepsB`)

Copies of `Ctx`/`Keeps`/`Ctx.keep`/`keeps_of` (W4Ctx) without the `x` operand and with only the frame slots `CtxB`
reads; `Ctx.ofB` adds the `x` facts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

/-- the window-4 context without `x` (before `x` is normalised / spilled) -/
def CtxB (R : RtInv) (L : List (Nat × Nat)) (g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat)
    (r29 : BitVec 64) (ex : List (Nat × Nat)) (M : Memory) : Prop :=
  Env R L g sp M ∧ CallW.CEnv R L g sp K 1040 M ∧ 4304 ≤ K ∧ K ≤ 2 ^ 20 ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  Inp R L sp n M mp ∧ Obj R L sp K st l0 ex M mp (8 * n) ∧ M.readLE mp (8 * n) = Mv ∧ NatNorm M mp n ∧
  Inp R L sp ylen M yp ∧ Obj R L sp K st l0 ex M yp (8 * ylen) ∧ M.readLE yp (8 * ylen) = Y ∧
  M.readLE (yp + 8 * (ylen - 1)) 8 = yi ∧ 0 < yi ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  zc < 2 ^ 40 ∧ (2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0 ∧ Obj R L sp K st l0 ex M zp (8 * zc) ∧
    Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  FinEnv sp g st n0 r29 ret M ∧ (InRanges st 24 L ∨ Outside st 24 R.rt) ∧ AW sp K st 24 ∧
  StkOK M R L st ∧ n0 ≤ l0 ∧ l0 ≤ stLen M st ∧ 0 < stCap M st ∧
  (0 < stCap M st → AW sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  Apart (stUp M st l0).1 (stUp M st l0).2 (g + 16) 8 ∧ AW sp K (stUp M st l0).1 (stUp M st l0).2 ∧
  Apart st 24 (stUp M st l0).1 (stUp M st l0).2 ∧
  RunIface.Globals R M [(sp - K, sp + 1040)] ∧ Obj R L sp K st l0 ex M RunIface.gA 32 ∧ Apart st 24 StackNat.wbA 4 ∧
  RoOut R ∧ Outside wT 16 R.rt ∧
  M.readLE (sp + 1016) 8 = mp ∧ M.readLE (sp + 1024) 8 = n ∧ M.readLE (sp + 1032) 8 = mc ∧
  M.readLE (sp + 952) 8 = zc ∧ M.readLE (sp + 936) 8 = zp ∧ M.readLE (sp + 1000) 8 = ylen ∧
  M.readLE (sp + 992) 8 = yp ∧ M.readLE (sp + 960) 8 = st

/-- `Keeps` with only the slots `CtxB` reads -/
def KeepsB (R : RtInv) (L L' : List (Nat × Nat)) (g sp K st l0 : Nat) (ex : List (Nat × Nat)) (M M' : Memory) : Prop :=
  LiveExt R L L' ∧ (∀ a k w, M'.accessible a k w = M.accessible a k w) ∧ CallW.CEnv R L' g sp K 1040 M' ∧
  (∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k) ∧
  (∀ j, (824 ≤ j ∧ j + 8 ≤ 896 ∨ 912 ≤ j ∧ j + 8 ≤ 1040) → M'.readLE (sp + j) 8 = M.readLE (sp + j) 8) ∧
  M'.readLE (sp - 8) 8 = M.readLE (sp - 8) 8 ∧ M'.readLE sp 8 = M.readLE sp 8 ∧
  M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 ∧
  StkOK M' R L' st ∧ stLen M st ≤ stLen M' st ∧
  ((stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
    (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L)) ∧
  (0 < stCap M st → 0 < stCap M' st)

set_option maxRecDepth 20000 in
theorem objB_keep {R : RtInv} {L L' : List (Nat × Nat)} {g sp K st l0 a k : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    (hk : KeepsB R L L' g sp K st l0 ex M M') (hl : l0 ≤ stCap M' st) (h : Obj R L sp K st l0 ex M a k) :
    Obj R L' sp K st l0 ex M' a k :=
  ⟨hk.1.held h.1, h.2.1, h.2.2.1, stUp_keep hk.2.2.2.2.2.2.2.2.2.2.1 h.1 h.2.2.2.1 hl, h.2.2.2.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxB.keep {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)} {M M' : Memory}
    (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    (hk : KeepsB R L L' g sp K st l0 ex M M') :
    CtxB R L' g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M' := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmv, hnm, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960⟩ := h
  have hk0 := hk
  obtain ⟨hx', hacc, hce', hrd, hsl, hsl8, hsl0, hgr, hsok', hlen, hst, hcp⟩ := hk0
  have rs : ∀ j, (824 ≤ j ∧ j + 8 ≤ 896 ∨ 912 ≤ j ∧ j + 8 ≤ 1040) → M'.readLE (sp + j) 8 = M.readLE (sp + j) 8 := hsl
  have hcap' : 0 < stCap M' st := hcp hcap
  have hl0' : l0 ≤ stCap M' st := Nat.le_trans hl0 (Nat.le_trans hlen hsok'.2.2.2.2.2.1)
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hce0 := hce
  obtain ⟨-, -, -, -, -, -, -, hrtK, hgaK, -, -, -, -⟩ := hce0
  have inp : ∀ k p, Inp R L sp k M p → Inp R L' sp k M' p := fun k p h =>
    ⟨by rw [hacc]; exact h.1, h.2.1, hx'.held h.2.2.1, h.2.2.2⟩
  refine ⟨?_, hce', hK, hK20, hn, hn128, hmc, hmc', inp _ _ hm, objB_keep hk hl0' hmO, by rw [hrd _ _ hmO]; exact hmv, ?_,
    inp _ _ hy, objB_keep hk hl0' hyO,
    by rw [hrd _ _ hyO]; exact hY, ?_, hyi0, hyl, hyl', hzc, ?_, ?_, hx'.held hsth, hstw, hsok', by omega,
    by omega, hcap', ?_, ?_, ?_, ?_, ?_, objB_keep hk hl0' hgO, hstwb, hro, hty,
    by rw [rs 1016 (by omega)]; exact r1016, by rw [rs 1024 (by omega)]; exact r1024,
    by rw [rs 1032 (by omega)]; exact r1032, by rw [rs 952 (by omega)]; exact r952,
    by rw [rs 936 (by omega)]; exact r936, by rw [rs 1000 (by omega)]; exact r1000,
    by rw [rs 992 (by omega)]; exact r992, by rw [rs 960 (by omega)]; exact r960⟩
  · -- Env
    refine ⟨hal, hsp1, hsp2, by rw [hacc]; exact hwacc, hg1, by rw [hacc]; exact hg2, by rw [hgr]; exact hg3, hwrt, hgw,
      hgrt, hx'.liveSep hLs ?_⟩
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 1040 - (sp - 4288) = 4288 + 1040 by omega]; exact hwrt
  · -- NatNorm
    rcases hnm with h | h
    · exact Or.inl h
    · right
      obtain ⟨o1, o2, o3, o4, o5⟩ := hmO
      simp only [AW, Apart, stUp] at o2 o3 o4
      have hn1 : mp + 8 * (n - 1) + 8 ≤ mp + 8 * n := by omega
      rw [hrd (mp + 8 * (n - 1)) 8 ⟨held_sub o1 (by omega) hn1,
        by simp only [AW, Apart]; omega, by unfold Apart; omega, by simp only [Apart, stUp]; omega,
        fun e he => by have := o5 e he; unfold Apart at this ⊢; omega⟩]
      exact h
  · obtain ⟨o1, o2, o3, o4, o5⟩ := hyO
    simp only [AW, Apart, stUp] at o2 o3 o4
    have hn1 : yp + 8 * (ylen - 1) + 8 ≤ yp + 8 * ylen := by omega
    rw [hrd (yp + 8 * (ylen - 1)) 8 ⟨held_sub o1 (by omega) hn1,
      by simp only [AW, Apart]; omega, by unfold Apart; omega, by simp only [Apart, stUp]; omega,
        fun e he => by have := o5 e he; unfold Apart at this ⊢; omega⟩]
    exact hyi
  · intro h2
    obtain ⟨b1, b2, b3, b4, b5⟩ := hz h2
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := b1
    exact ⟨⟨c1, c2, by rw [hacc]; exact c3, c4, hx'.held c5, c6, c7⟩, b2, objB_keep hk hl0' b3, b4, b5⟩
  · -- FinEnv
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hfe
    have hc2 : n0 ≤ stCap M' st := by
      have := hsok'.2.2.2.2.2.1; simp only [stLen] at hlen this; omega
    refine ⟨f1, f2, f3, by rw [hacc]; exact f4, f5, by rw [hacc]; exact f6, by rw [hgr]; exact f7, f8,
      by rw [rs 912 (by omega)]; exact f9, by rw [rs 840 (by omega)]; exact f10, by rw [rs 848 (by omega)]; exact f11,
      by rw [rs 856 (by omega)]; exact f12, f13, by rw [hacc]; exact f14, hc2, f16, f17,
      by rw [hsl8]; exact f18, by rw [hsl0]; exact f19⟩
  · -- the whole array
    intro hc
    rcases hst with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e1, e2]; rw [e2] at hc; exact harr hc
    · have h1 := out_inR hrtK hin
      have h2 := out_inR hgrt hin
      simp only [AW, Apart]; omega
  · exact stUp_keep_out hst hgrt hug hl0'
  · exact stUp_keep_out hst hrtK huw hl0'
  · exact stUp_keep hst hsth hsu hl0'
  · -- Globals
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hgl
    have hrdG : ∀ j, j + 8 ≤ 32 → M'.readLE (RunIface.gA + j) 8 = M.readLE (RunIface.gA + j) 8 := by
      intro j hj
      obtain ⟨o1, o2, o3, o4, o5⟩ := hgO
      simp only [AW, Apart, stUp] at o2 o3 o4
      exact hrd _ _ ⟨o1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)),
        by simp only [AW, Apart]; omega, by unfold Apart; omega, by simp only [Apart, stUp]; omega,
        fun e he => by have := o5 e he; unfold Apart at this ⊢; omega⟩
    refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hacc]; exact g8, g9, g10, by rw [hacc]; exact g11, g12, g13⟩
    · rw [g5, hrdG 8 (by omega), ← g5]; exact g1
    · rw [g6, hrdG 16 (by omega), ← g6]; exact g2
    · rw [g7, hrdG 24 (by omega), ← g7]; exact g3
    · have := hrdG 0 (by omega); simp only [Nat.add_zero] at this
      show M'.readLE RunIface.gA 8 = 40; rw [this]; exact g4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `Keeps` from a step's frames: `MemFrame` over `R.rt ++ ws`, `LiveFrame` exempting `ws'`, both lists outside every
context object, the kept slots and the guard word -/
theorem keeps_ofB {R : RtInv} {L L' : List (Nat × Nat)} {g sp K st l0 : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    {ws ws' : List (Nat × Nat)} (hce : CallW.CEnv R L g sp K 1040 M) (hK4 : 4304 ≤ K) (hx : LiveExt R L L')
    (hF : MemFrame M M' (R.rt ++ ws)) (hL : LiveFrame M M' L ws') (hreg : M'.regions = M.regions)
    (hwa : ∀ r ∈ ws, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true) (hg : Outside (g + 16) 8 ws)
    (hobj : ∀ a k, Obj R L sp K st l0 ex M a k → Outside a k ws ∧ Outside a k ws')
    (hsl : ∀ j, (824 ≤ j ∧ j + 8 ≤ 896 ∨ 912 ≤ j ∧ j + 8 ≤ 1040) → Outside (sp + j) 8 ws)
    (hsl8 : Outside (sp - 8) 8 ws) (hsl0 : Outside sp 8 ws)
    (hsok : StkOK M' R L' st) (hlen : stLen M st ≤ stLen M' st)
    (hst : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hcp : 0 < stCap M st → 0 < stCap M' st) :
    KeepsB R L L' g sp K st l0 ex M M' := by
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hce1 := CallW.CEnv.frame hce hF hreg hwa hg
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hce1
  have hwin : ∀ j, sp - K ≤ j → j + 8 ≤ sp + 1040 → Outside j 8 R.rt := fun j h1 h2 => hrt.of_sub h1 (by omega)
  refine ⟨hx, fun a k w => hF.accessible a k w, ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hx.liveSep c11 ?_, c12, c13⟩,
    fun a k ho => ?_, fun j hj => ?_, ?_, ?_, ?_, hsok, hlen, hst, hcp⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 1040 - (sp - K) = K + 1040 by omega]; exact hrt
  · obtain ⟨o1, o2⟩ := hobj a k ho
    rcases ho.1 with h | h
    · exact hL.readLE a k h o2
    · exact hF.readLE a k (by rw [outside_append]; exact ⟨h, o1⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hwin _ (by omega) (by omega), hsl j hj⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hwin _ (by omega) (by omega), hsl8⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hwin _ (by omega) (by omega), hsl0⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hg⟩)

/-- `CtxB` plus the (normalised, `n`-word) `x` and its spills is `Ctx` -/
theorem Ctx.ofB {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {M : Memory} (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    (hx : Inp R L sp n M xp) (hxO : Obj R L sp K st l0 ex M xp (8 * n)) (hxv : M.readLE xp (8 * n) = Xv)
    (r904 : M.readLE (sp + 904) 8 = xp) (r328 : M.readLE (sp + 328) 8 = n) (r320 : M.readLE (sp + 320) 8 = xc) :
    Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960⟩ := h
  exact ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960, r904, r328, r320⟩

/-- `Keeps` gives `KeepsB` -/
theorem Keeps.toB {R : RtInv} {L L' : List (Nat × Nat)} {g sp K st l0 : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    (h : Keeps R L L' g sp K st l0 ex M M') : KeepsB R L L' g sp K st l0 ex M M' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨a1, a2, a3, a4, fun j hj => a5 j (by omega), a6⟩

/-- `Anc` through a `KeepsB` step -/
theorem Anc.keepB {R : RtInv} {L0 L L' : List (Nat × Nat)} {g sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : Anc R L0 sp K st M0 L M) (hk : KeepsB R L L' g sp K st l0 ex M M')
    (hl0 : stLen M0 st ≤ l0) (hl0' : l0 ≤ stCap M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e)
    (hLs : LiveSep L [(sp - K, sp + 1040)]) (hK : K ≤ sp) : Anc R L0 sp K st M0 L' M' :=
  Anc.step hA hk.1 hk.2.1 hk.2.2.2.1 (hk.2.2.2.2.1 920 (by omega)) (hk.2.2.2.2.1 928 (by omega))
    hk.2.2.2.2.2.2.2.2.2.1 hk.2.2.2.2.2.2.2.2.2.2.1 hl0 hl0' hex hLs hK

end FvModexp.Arm64.W4Pro
