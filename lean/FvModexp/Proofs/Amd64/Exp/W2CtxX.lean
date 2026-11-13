import FvModexp.Proofs.Amd64.Exp.W2Own

set_option autoImplicit false

/-!
# window-2 prologue (amd64): the context before `x` and `n` are spilled (`CtxX`) and its transfer (`KeepsX`)
(agent expmc s54; role of `Arm64.W2CtxB`)

Mechanical copies of `KeptJ`/`Ctx`/`Keeps`/`obj_keep`/`fin_keep`/`Ctx.keep`/`keeps_of` (W2Ctx): `CtxX` is `Ctx` without
the two frame slots `[0x258] = xp`, `[0x138] = n` (spilled only by `toSn1`), and `KeptJX` keeps only the input/defer
slots `[0x228, 0x240) ∪ [0x260, 0x2a8)` and `5n` at 0x148 (so `toSn1`'s and the `x` normalisation's own stores are allowed). `Ctx.ofX` adds the two slots.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- the own slots kept before `toSn1`: the defer record `[0x228, 0x240)` and the input/defer slots
`[0x260, 0x2a8)`, and `5n` (0x148, spilled at the entry) (the `x` normalisation spills to 0x250, `toSn1` to 0x258) -/
@[reducible] def KeptJX (j : Nat) : Prop :=
  0x148 ≤ j ∧ j + 8 ≤ 0x150 ∨ 0x228 ≤ j ∧ j + 8 ≤ 0x240 ∨ 0x260 ≤ j ∧ j + 8 ≤ 0x2a8

/-- the window-2 context (values `Mv` of `m[0:n]`, `Xv` of `x[0:n]`, `Y` of `y`) -/
def CtxX (R : RtInv) (L : List (Nat × Nat)) (g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat)
    (ex : List (Nat × Nat)) (M : Memory) : Prop :=
  Env R L g fs sp M ∧ CallW.CEnv R L g fs (sp - 8) K 688 M ∧ 41512 ≤ K ∧ K ≤ 2 ^ 20 ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  Inp R L sp n M mp ∧ Obj R L sp K st l0 ex M mp (8 * n) ∧ M.readLE mp (8 * n) = Mv ∧ NatNorm M mp n ∧
  Inp R L sp n M xp ∧ Obj R L sp K st l0 ex M xp (8 * n) ∧ M.readLE xp (8 * n) = Xv ∧
  Inp R L sp ylen M yp ∧ Obj R L sp K st l0 ex M yp (8 * ylen) ∧ M.readLE yp (8 * ylen) = Y ∧
  M.readLE (yp + 8 * (ylen - 1)) 8 = yi ∧ 0 < yi ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  zc < 2 ^ 40 ∧ (2 * n ≤ zc → Buf R L g fs sp n M zp zc ∧ zp % 8 = 0 ∧ Obj R L sp K st l0 ex M zp (8 * zc) ∧
    Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  FinEnv sp st n0 fbp r M ∧ (InRanges st 24 L ∨ Outside st 24 R.rt) ∧ AW sp K st 24 ∧
  StkOK M R L st ∧ n0 ≤ l0 ∧ l0 ≤ stLen M st ∧ 0 < stCap M st ∧
  (0 < stCap M st → AW sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧
    Apart (stW M st) (8 * stCap M st) (fs - 8) 8) ∧
  Apart (stUp M st l0).1 (stUp M st l0).2 (g + 16) 8 ∧ Apart (stUp M st l0).1 (stUp M st l0).2 (fs - 8) 8 ∧
  AW sp K (stUp M st l0).1 (stUp M st l0).2 ∧ Apart st 24 (stUp M st l0).1 (stUp M st l0).2 ∧
  Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  RunIface.Globals R M [(sp - 8 - K, sp + 0x2a8)] ∧ Obj R L sp K st l0 ex M RunIface.gA 32 ∧
  Apart st 24 StackNat.wbA 4 ∧ M.accessible StackNat.wbA 4 false = true ∧
  M.accessible (sp + 0x2a8) 0x20 false = true ∧ Outside (sp + 0x2a8) 0x20 R.rt ∧
  Obj R L sp K st l0 ex M (sp + 0x2a8) 0x20 ∧
  M.readLE (sp + 0x290) 8 = mp ∧ M.readLE (sp + 0x298) 8 = n ∧ M.readLE (sp + 0x2a0) 8 = mc ∧
  M.readLE (sp + 0x2b8) 8 = zc ∧ M.readLE (sp + 0x2a8) 8 = zp ∧ M.readLE (sp + 0x280) 8 = ylen ∧
  M.readLE (sp + 0x278) 8 = yp ∧ M.readLE (sp + 0x2c0) 8 = st ∧
  M.readLE (sp + 0x148) 8 = 5 * n ∧ st ≠ 0

/-- what a step `M → M'` (live set `L → L'`) of the `RR` section keeps -/
def KeepsX (R : RtInv) (L L' : List (Nat × Nat)) (g fs sp K st l0 : Nat) (ex : List (Nat × Nat)) (M M' : Memory) :
    Prop :=
  LiveExt R L L' ∧ (∀ a k w, M'.accessible a k w = M.accessible a k w) ∧ CallW.CEnv R L' g fs (sp - 8) K 688 M' ∧
  (∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k) ∧
  (∀ j, KeptJX j → M'.readLE (sp + j) 8 = M.readLE (sp + j) 8) ∧
  M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 ∧ M'.readLE (fs - 8) 8 = M.readLE (fs - 8) 8 ∧
  StkOK M' R L' st ∧ stLen M st ≤ stLen M' st ∧
  ((stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
    (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L)) ∧
  (0 < stCap M st → 0 < stCap M' st) ∧ ArrIn L' st M M'

set_option maxRecDepth 20000 in
theorem obj_keepX {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp K st l0 a k : Nat} {ex : List (Nat × Nat)}
    {M M' : Memory} (hk : KeepsX R L L' g fs sp K st l0 ex M M') (hl : l0 ≤ stCap M' st)
    (h : Obj R L sp K st l0 ex M a k) : Obj R L' sp K st l0 ex M' a k :=
  ⟨hk.1.held h.1, h.2.1, h.2.2.1, stUp_keep hk.2.2.2.2.2.2.2.2.2.1 h.1 h.2.2.2.1 hl, h.2.2.2.2⟩

theorem fin_keepX {sp st n0 fbp r l0 : Nat} {M M' : Memory} (hfe : FinEnv sp st n0 fbp r M)
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (rs : ∀ j, KeptJX j → M'.readLE (sp + j) 8 = M.readLE (sp + j) 8) (hn0 : n0 ≤ l0) (hl : l0 ≤ stCap M' st) :
    FinEnv sp st n0 fbp r M' := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
  refine ⟨f1, f2, f3, by rw [hacc]; exact f4, by rw [rs 0x260 (by simp only [KeptJX]; omega)]; exact f5,
    by rw [rs 0x228 (by simp only [KeptJX]; omega)]; exact f6, by rw [rs 0x230 (by simp only [KeptJX]; omega)]; exact f7,
    by rw [rs 0x238 (by simp only [KeptJX]; omega)]; exact f8, f9, by rw [hacc]; exact f10, ?_, f12,
    by rw [rs 0x268 (by simp only [KeptJX]; omega)]; exact f13, by rw [rs 0x270 (by simp only [KeptJX]; omega)]; exact f14,
    f15⟩
  simp only [stCap] at hl; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxX.keep {R : RtInv} {L L' : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    (hk : KeepsX R L L' g fs sp K st l0 ex M M') :
    CtxX R L' g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M' := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmv, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huf, huw, hsu, hstg, hstf, hgl, hgO, hstwb, hwba,
    hcacc, hcrt, hcO, r3a8, r3b0, r3b8, r3d0, r3c0, r398, r390, r3d8, r148, hstnz⟩ := h
  have hk0 := hk
  obtain ⟨hx', hacc, hce', hrd, rs, hgr, hfr, hsok', hlen, hst, hcp, -⟩ := hk0
  have hcap' : 0 < stCap M' st := hcp hcap
  have hl0' : l0 ≤ stCap M' st := Nat.le_trans hl0 (Nat.le_trans hlen hsok'.2.2.2.2.2.1)
  have hce0 := hce
  obtain ⟨-, -, -, -, -, -, -, hrtK, hgaK, hgrt, -, -, -, -, -, -, -, hfrt, -⟩ := hce0
  have inp : ∀ k p, Inp R L sp k M p → Inp R L' sp k M' p := fun k p h =>
    ⟨by rw [hacc]; exact h.1, h.2.1, hx'.held h.2.2.1, h.2.2.2⟩
  have rc : ∀ j, j + 8 ≤ 0x20 → M'.readLE (sp + 0x2a8 + j) 8 = M.readLE (sp + 0x2a8 + j) 8 :=
    fun j hj => hrd _ _ (obj_sub hcO (by omega) (by omega))
  refine ⟨env_keep he hx' hacc hgr hfr, hce', hK, hK20, hn, hn128, hmc, hmc', inp _ _ hm, obj_keepX hk hl0' hmO,
    by rw [hrd _ _ hmO]; exact hmv, ?_,
    inp _ _ hx, obj_keepX hk hl0' hxO, by rw [hrd _ _ hxO]; exact hxv, inp _ _ hy, obj_keepX hk hl0' hyO,
    by rw [hrd _ _ hyO]; exact hY, ?_, hyi0, hyl, hyl', hzc, ?_, fin_keepX hfe hacc rs hn0 hl0', hx'.held hsth, hstw,
    hsok', by omega, by omega, hcap', ?_, stUp_keep_out hst hgrt hug hl0', stUp_keep_out hst hfrt huf hl0',
    stUp_keep_out hst hrtK huw hl0', stUp_keep hst hsth hsu hl0', hstg, hstf, globals_keep hgl hgO hacc hrd,
    obj_keepX hk hl0' hgO, hstwb, by rw [hacc]; exact hwba, by rw [hacc]; exact hcacc, hcrt, obj_keepX hk hl0' hcO,
    by rw [rs 0x290 (by simp only [KeptJX]; omega)]; exact r3a8, by rw [rs 0x298 (by simp only [KeptJX]; omega)]; exact r3b0,
    by rw [rs 0x2a0 (by simp only [KeptJX]; omega)]; exact r3b8,
    by rw [show sp + 0x2b8 = sp + 0x2a8 + 16 by omega, rc 16 (by omega)]; exact r3d0,
    by rw [show sp + 0x2a8 = sp + 0x2a8 + 0 by omega, rc 0 (by omega)]; exact r3c0,
    by rw [rs 0x280 (by simp only [KeptJX]; omega)]; exact r398, by rw [rs 0x278 (by simp only [KeptJX]; omega)]; exact r390,
    by rw [show sp + 0x2c0 = sp + 0x2a8 + 24 by omega, rc 24 (by omega)]; exact r3d8,
    by rw [rs 0x148 (by simp only [KeptJX]; omega)]; exact r148, hstnz⟩
  · -- NatNorm
    rcases hnm with h | h
    · exact Or.inl h
    · right
      have hn1 : mp + 8 * (n - 1) + 8 ≤ mp + 8 * n := by omega
      rw [hrd (mp + 8 * (n - 1)) 8 (obj_sub hmO (by omega) hn1)]
      exact h
  · have hn1 : yp + 8 * (ylen - 1) + 8 ≤ yp + 8 * ylen := by omega
    rw [hrd (yp + 8 * (ylen - 1)) 8 (obj_sub hyO (by omega) hn1)]
    exact hyi
  · intro h2
    obtain ⟨b1, b2, b3, b4, b5⟩ := hz h2
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := b1
    exact ⟨⟨c1, c2, by rw [hacc]; exact c3, c4, hx'.held c5, c6, c7, c8⟩, b2, obj_keepX hk hl0' b3, b4, b5⟩
  · -- the whole array
    intro hc
    rcases hst with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e1, e2]; rw [e2] at hc; exact harr hc
    · have h1 := out_inR hrtK hin
      have h2 := out_inR hgrt hin
      have h3 := out_inR hfrt hin
      simp only [AW, Apart]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `KeepsX` from a step's frames: `MemFrame` over `R.rt ++ ws`, `LiveFrame` exempting `ws'`, both lists outside every
context object, the kept slots and the guard / TLS words -/
theorem keeps_ofX {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp K st l0 : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    {ws ws' : List (Nat × Nat)} (hce : CallW.CEnv R L g fs (sp - 8) K 688 M) (hx : LiveExt R L L')
    (hF : MemFrame M M' (R.rt ++ ws)) (hL : LiveFrame M M' L ws') (hreg : M'.regions = M.regions)
    (hwa : ∀ r ∈ ws, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true) (hg : Outside (g + 16) 8 ws)
    (hfw : Outside (fs - 8) 8 ws)
    (hobj : ∀ a k, Obj R L sp K st l0 ex M a k → Outside a k ws ∧ Outside a k ws')
    (hsl : ∀ j, KeptJX j → Outside (sp + j) 8 ws)
    (hsok : StkOK M' R L' st) (hlen : stLen M st ≤ stLen M' st)
    (hst : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hcp : 0 < stCap M st → 0 < stCap M' st) (hai : ArrIn L' st M M') :
    KeepsX R L L' g fs sp K st l0 ex M M' := by
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have hce1 := CallW.CEnv.frame hce hF hreg hwa hg hfw
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, d1, d2, d3, d4, d5, d6⟩ := hce1
  refine ⟨hx, fun a k w => hF.accessible a k w,
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hx.liveSep c11 ?_, c12, c13, d1, d2, d3, d4, d5, d6⟩,
    fun a k ho => ?_, fun j hj => ?_, ?_, ?_, hsok, hlen, hst, hcp, hai⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp - 8 + 688 - (sp - 8 - K) = K + 688 by omega]; exact hrt
  · obtain ⟨o1, o2⟩ := hobj a k ho
    rcases ho.1 with h | h
    · exact hL.readLE a k h o2
    · exact hF.readLE a k (by rw [outside_append]; exact ⟨h, o1⟩)
  · have hj' := hj; simp only [KeptJX] at hj'
    exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hrt.of_sub (by omega) (by omega), hsl j hj⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hg⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨f5, hfw⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the frame's own stores (inside `[sp - 8, sp + 0x2a8)`, off the kept slots) keep the context -/
theorem keeps_ownX {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hreg : M'.regions = M.regions)
    (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x2a8) (hsl : ∀ j, KeptJX j → Outside (sp + j) 8 ws) :
    KeepsX R L L g fs sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have hin' : ∀ q ∈ ws, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp - 8 + 688 := fun q hq => by have := hin q hq; omega
  have ow : ∀ a k, Apart a k (sp - 8 - K) (K + 688) → Outside a k ws := fun a k h =>
    outside_ws_of_win (by unfold Apart at h; omega) hin'
  have hst : Apart st 24 (sp - 8 - K) (K + 688) := hstw
  have e0 := hF.readLE st 8 (ow _ _ (hst.mono (by omega) (Nat.le_refl _)))
  have e1 := hF.readLE (st + 8) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have e2 := hF.readLE (st + 16) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have hsok' := stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w)
  refine keeps_ofX hce (LiveExt.refl R L) (FvModexp.Expmc.frame_widen_rt hF)
    (FvModexp.Expmc.liveFrame_of_frame (ws := ([] : List (Nat × Nat))) hF (fun a k hin2 _ => ?_)) hreg ?_
    (ow _ _ hga) (ow _ _ f6) (fun a k ho => ⟨ow _ _ ho.2.1, trivial⟩) hsl hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _) (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
    (arrIn_kept ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
  · obtain ⟨q, hq, h1, h2⟩ := hin2
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this
    exact outside_ws_of_win (lo := sp - 8 - K) (hi := sp - 8 + 688) (by omega) hin'
  · intro q hq hlt
    have := hin q hq
    exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)

/-- `CtxX` plus the two spilled slots is `Ctx` -/
theorem Ctx.ofX {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    (r370 : M.readLE (sp + 0x258) 8 = xp) (r138 : M.readLE (sp + 0x140) 8 = n) :
    Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
    h43, h44, h45, r1, r2, r3, r4, r5, r6, r7, r8, r148, hstnz⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
    h43, h44, h45, r1, r2, r3, r4, r5, r6, r7, r8, r370, r138, r148, hstnz⟩

end FvModexp.Amd64.W2Pro
