import FvModexp.Proofs.Amd64.Exp.W4RRRet
import FvModexp.Proofs.Amd64.Exp.W4ZmDefs

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the context of the `RR` section and its transfer through a step
(agent expmc s52; twin of `Arm64.W4Ctx`)

`Ctx` bundles the facts the rest of window-4 needs about the operands, the frame and the stack that every step of the
`RR` section (`stk.nat`, `lsh`, `stk.nat`, `div`, own spills) keeps. The caller window is PARAMETRIC in the deepest
callee window `K` (`CallW.CEnv … (sp - 8) K 968`, `K ≥ 41512` for asm's `nat.div`); the loop's fixed `Env`
(`[sp - 4296, sp + 0x3c0)`) is kept alongside. `stUp M st l0` is the part of the stack's array above the level `l0`.
The caller-argument slots `[sp + 0x3c0, sp + 0x3e0)` (z, z.len, z.cap, stk of `expNNWindowed`) are a context object.
`Ctx.keep` moves the context through any step given the step's `Keeps` facts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- the stack array above level `l0` -/
@[reducible] def stUp (M : Memory) (st l0 : Nat) : Nat × Nat := (stW M st + 8 * l0, 8 * (stCap M st - l0))

/-- the window-4 frame below `sp + 0x3c0` with the deepest callee window `K` (= `W4Div.AWx`) -/
@[reducible] def AW (sp K a k : Nat) : Prop := Apart a k (sp - 8 - K) (K + 968)

/-- an object of the context: held, apart from the frame, from the stack header and from the stack above `l0` -/
@[reducible] def Obj (R : RtInv) (L : List (Nat × Nat)) (sp K st l0 : Nat) (ex : List (Nat × Nat)) (M : Memory)
    (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ AW sp K a k ∧ Apart a k st 24 ∧ Apart a k (stUp M st l0).1 (stUp M st l0).2 ∧
    ∀ e ∈ ex, Apart a k e.1 e.2

/-- the own slots every step of the `RR` section keeps (`sp + j`, 8 bytes): `2n` (0x78), `zz` (0x188/0x98/0xa0),
`RR` (0x190/0xa8), `t` (0xd8), `n`/`xc` (0x138/0x140), the input/defer slots `[0x340, 0x3c0)` -/
@[reducible] def KeptJ (j : Nat) : Prop :=
  0x78 ≤ j ∧ j + 8 ≤ 0x80 ∨ 0x98 ≤ j ∧ j + 8 ≤ 0xb0 ∨ 0xd8 ≤ j ∧ j + 8 ≤ 0xe0 ∨ 0x138 ≤ j ∧ j + 8 ≤ 0x148 ∨
    0x188 ≤ j ∧ j + 8 ≤ 0x198 ∨ 0x340 ≤ j ∧ j + 8 ≤ 0x3c0

/-- the window-4 context (values `Mv` of `m[0:n]`, `Xv` of `x[0:n]`, `Y` of `y`) -/
def Ctx (R : RtInv) (L : List (Nat × Nat)) (g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat)
    (ex : List (Nat × Nat)) (M : Memory) : Prop :=
  Env R L g fs sp M ∧ CallW.CEnv R L g fs (sp - 8) K 968 M ∧ 41512 ≤ K ∧ K ≤ 2 ^ 20 ∧
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
  RunIface.Globals R M [(sp - 8 - K, sp + 0x3c0)] ∧ Obj R L sp K st l0 ex M RunIface.gA 32 ∧
  Apart st 24 StackNat.wbA 4 ∧ M.accessible StackNat.wbA 4 false = true ∧
  M.accessible (sp + 0x3c0) 0x20 false = true ∧ Outside (sp + 0x3c0) 0x20 R.rt ∧
  Obj R L sp K st l0 ex M (sp + 0x3c0) 0x20 ∧
  M.readLE (sp + 0x3a8) 8 = mp ∧ M.readLE (sp + 0x3b0) 8 = n ∧ M.readLE (sp + 0x3b8) 8 = mc ∧
  M.readLE (sp + 0x3d0) 8 = zc ∧ M.readLE (sp + 0x3c0) 8 = zp ∧ M.readLE (sp + 0x398) 8 = ylen ∧
  M.readLE (sp + 0x390) 8 = yp ∧ M.readLE (sp + 0x3d8) 8 = st ∧
  M.readLE (sp + 0x370) 8 = xp ∧ M.readLE (sp + 0x138) 8 = n

/-- what a step `M → M'` (live set `L → L'`) of the `RR` section keeps -/
def Keeps (R : RtInv) (L L' : List (Nat × Nat)) (g fs sp K st l0 : Nat) (ex : List (Nat × Nat)) (M M' : Memory) :
    Prop :=
  LiveExt R L L' ∧ (∀ a k w, M'.accessible a k w = M.accessible a k w) ∧ CallW.CEnv R L' g fs (sp - 8) K 968 M' ∧
  (∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k) ∧
  (∀ j, KeptJ j → M'.readLE (sp + j) 8 = M.readLE (sp + j) 8) ∧
  M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 ∧ M'.readLE (fs - 8) 8 = M.readLE (fs - 8) 8 ∧
  StkOK M' R L' st ∧ stLen M st ≤ stLen M' st ∧
  ((stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
    (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L)) ∧
  (0 < stCap M st → 0 < stCap M' st) ∧ ArrIn L' st M M'

/-- a step that keeps the stack's array keeps `ArrIn` -/
theorem arrIn_kept {L : List (Nat × Nat)} {st : Nat} {M M' : Memory}
    (h : stW M' st = stW M st ∧ stCap M' st = stCap M st) : ArrIn L st M M' := fun hn => absurd h hn

theorem held_sub {R : RtInv} {L : List (Nat × Nat)} {a n b k : Nat} (h : InRanges b k L ∨ Outside b k R.rt)
    (h1 : b ≤ a) (h2 : a + n ≤ b + k) : InRanges a n L ∨ Outside a n R.rt :=
  h.imp (fun h => h.sub h1 h2) (fun h => h.of_sub h1 h2)

theorem apart_fresh {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart a n p k := apart_held' hin hap hh

/-- apartness from the whole stack array gives apartness from the part above `l0` -/
theorem up_of_arr {a k st l0 : Nat} {M : Memory} (h : Apart a k (stW M st) (8 * stCap M st)) (hl : l0 ≤ stCap M st) :
    Apart a k (stUp M st l0).1 (stUp M st l0).2 := by
  simp only [stUp]; unfold Apart at h ⊢; omega

/-- apartness from the part above `l0` gives apartness from the free part (`l0 ≤ len ≤ cap`) -/
theorem free_of_up {a k st l0 : Nat} {M : Memory} (h : Apart a k (stUp M st l0).1 (stUp M st l0).2)
    (hl : l0 ≤ stLen M st) (hlc : stLen M st ≤ stCap M st) : Apart a k (stFree M st).1 (stFree M st).2 := by
  simp only [stUp, stFree] at h ⊢; unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
/-- the stack above `l0` after a step: same array, or a fresh one apart from every held object -/
theorem stUp_keep {R : RtInv} {L : List (Nat × Nat)} {st l0 a k : Nat} {M M' : Memory}
    (hs : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hh : InRanges a k L ∨ Outside a k R.rt) (ha : Apart a k (stUp M st l0).1 (stUp M st l0).2)
    (hl : l0 ≤ stCap M' st) :
    Apart a k (stUp M' st l0).1 (stUp M' st l0).2 := by
  rcases hs with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · simp only [stUp] at ha ⊢; rw [e1, e2]; exact ha
  · have := apart_fresh hin hap hh
    simp only [stUp]; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- a region outside `R.rt` stays apart from the stack above `l0` -/
theorem stUp_keep_out {R : RtInv} {L : List (Nat × Nat)} {st l0 a k : Nat} {M M' : Memory}
    (hs : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hrt : Outside a k R.rt) (ha : Apart (stUp M st l0).1 (stUp M st l0).2 a k) (hl : l0 ≤ stCap M' st) :
    Apart (stUp M' st l0).1 (stUp M' st l0).2 a k := by
  have := stUp_keep (l0 := l0) hs (Or.inr hrt) (by unfold Apart at ha ⊢; omega) hl
  unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
theorem obj_keep {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp K st l0 a k : Nat} {ex : List (Nat × Nat)}
    {M M' : Memory} (hk : Keeps R L L' g fs sp K st l0 ex M M') (hl : l0 ≤ stCap M' st)
    (h : Obj R L sp K st l0 ex M a k) : Obj R L' sp K st l0 ex M' a k :=
  ⟨hk.1.held h.1, h.2.1, h.2.2.1, stUp_keep hk.2.2.2.2.2.2.2.2.2.1 h.1 h.2.2.2.1 hl, h.2.2.2.2⟩

/-- an 8-byte read inside a context object is kept -/
theorem obj_sub {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 a k b : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : Obj R L sp K st l0 ex M a k) (h1 : a ≤ b) (h2 : b + 8 ≤ a + k) : Obj R L sp K st l0 ex M b 8 := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := h
  simp only [AW, Apart, stUp] at o2 o3 o4
  exact ⟨held_sub o1 h1 h2, by simp only [AW, Apart]; omega, by unfold Apart; omega,
    by simp only [Apart, stUp]; omega, fun e he => by have := o5 e he; unfold Apart at this ⊢; omega⟩

theorem env_keep {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp : Nat} {M M' : Memory} (he : Env R L g fs sp M)
    (hx : LiveExt R L L') (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8) (hfr : M'.readLE (fs - 8) 8 = M.readLE (fs - 8) 8) :
    Env R L' g fs sp M' := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs, hf2, hf3, hf4, hf5, hadx⟩ := he
  refine ⟨hal, hsp1, hsp2, by rw [hacc]; exact hwacc, hg1, by rw [hacc]; exact hg2, by rw [hgr]; exact hg3, hwrt, hgw,
    hgrt, hx.liveSep hLs ?_, hfs, by rw [hacc]; exact hf2, by rw [hfr]; exact hf3, hf4, hf5, by rw [hacc]; exact hadx⟩
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only; rw [show sp + 0x3c0 - (sp - 4296) = 4296 + 0x3c0 by omega]; exact hwrt

theorem fin_keep {sp st n0 fbp r l0 : Nat} {M M' : Memory} (hfe : FinEnv sp st n0 fbp r M)
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (rs : ∀ j, KeptJ j → M'.readLE (sp + j) 8 = M.readLE (sp + j) 8) (hn0 : n0 ≤ l0) (hl : l0 ≤ stCap M' st) :
    FinEnv sp st n0 fbp r M' := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
  refine ⟨f1, f2, f3, by rw [hacc]; exact f4, by rw [rs 0x378 (by simp only [KeptJ]; omega)]; exact f5,
    by rw [rs 0x340 (by simp only [KeptJ]; omega)]; exact f6, by rw [rs 0x348 (by simp only [KeptJ]; omega)]; exact f7,
    by rw [rs 0x350 (by simp only [KeptJ]; omega)]; exact f8, f9, by rw [hacc]; exact f10, ?_, f12,
    by rw [rs 0x380 (by simp only [KeptJ]; omega)]; exact f13, by rw [rs 0x388 (by simp only [KeptJ]; omega)]; exact f14,
    f15⟩
  simp only [stCap] at hl; omega

set_option maxRecDepth 20000 in
theorem globals_keep {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    {w : List (Nat × Nat)} (hgl : RunIface.Globals R M w) (hgO : Obj R L sp K st l0 ex M RunIface.gA 32)
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (hrd : ∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k) : RunIface.Globals R M' w := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hgl
  have hrdG : ∀ j, j + 8 ≤ 32 → M'.readLE (RunIface.gA + j) 8 = M.readLE (RunIface.gA + j) 8 :=
    fun j hj => hrd _ _ (obj_sub hgO (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hacc]; exact g8, g9, g10, by rw [hacc]; exact g11, g12, g13⟩
  · rw [g5, hrdG 8 (by omega), ← g5]; exact g1
  · rw [g6, hrdG 16 (by omega), ← g6]; exact g2
  · rw [g7, hrdG 24 (by omega), ← g7]; exact g3
  · have := hrdG 0 (by omega); simp only [Nat.add_zero] at this
    show M'.readLE RunIface.gA 8 = 40; rw [this]; exact g4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem Ctx.keep {R : RtInv} {L L' : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    (h : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    (hk : Keeps R L L' g fs sp K st l0 ex M M') :
    Ctx R L' g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M' := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmv, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huf, huw, hsu, hstg, hstf, hgl, hgO, hstwb, hwba,
    hcacc, hcrt, hcO, r3a8, r3b0, r3b8, r3d0, r3c0, r398, r390, r3d8, r370, r138⟩ := h
  have hk0 := hk
  obtain ⟨hx', hacc, hce', hrd, rs, hgr, hfr, hsok', hlen, hst, hcp, -⟩ := hk0
  have hcap' : 0 < stCap M' st := hcp hcap
  have hl0' : l0 ≤ stCap M' st := Nat.le_trans hl0 (Nat.le_trans hlen hsok'.2.2.2.2.2.1)
  have hce0 := hce
  obtain ⟨-, -, -, -, -, -, -, hrtK, hgaK, hgrt, -, -, -, -, -, -, -, hfrt, -⟩ := hce0
  have inp : ∀ k p, Inp R L sp k M p → Inp R L' sp k M' p := fun k p h =>
    ⟨by rw [hacc]; exact h.1, h.2.1, hx'.held h.2.2.1, h.2.2.2⟩
  have rc : ∀ j, j + 8 ≤ 0x20 → M'.readLE (sp + 0x3c0 + j) 8 = M.readLE (sp + 0x3c0 + j) 8 :=
    fun j hj => hrd _ _ (obj_sub hcO (by omega) (by omega))
  refine ⟨env_keep he hx' hacc hgr hfr, hce', hK, hK20, hn, hn128, hmc, hmc', inp _ _ hm, obj_keep hk hl0' hmO,
    by rw [hrd _ _ hmO]; exact hmv, ?_,
    inp _ _ hx, obj_keep hk hl0' hxO, by rw [hrd _ _ hxO]; exact hxv, inp _ _ hy, obj_keep hk hl0' hyO,
    by rw [hrd _ _ hyO]; exact hY, ?_, hyi0, hyl, hyl', hzc, ?_, fin_keep hfe hacc rs hn0 hl0', hx'.held hsth, hstw,
    hsok', by omega, by omega, hcap', ?_, stUp_keep_out hst hgrt hug hl0', stUp_keep_out hst hfrt huf hl0',
    stUp_keep_out hst hrtK huw hl0', stUp_keep hst hsth hsu hl0', hstg, hstf, globals_keep hgl hgO hacc hrd,
    obj_keep hk hl0' hgO, hstwb, by rw [hacc]; exact hwba, by rw [hacc]; exact hcacc, hcrt, obj_keep hk hl0' hcO,
    by rw [rs 0x3a8 (by simp only [KeptJ]; omega)]; exact r3a8, by rw [rs 0x3b0 (by simp only [KeptJ]; omega)]; exact r3b0,
    by rw [rs 0x3b8 (by simp only [KeptJ]; omega)]; exact r3b8,
    by rw [show sp + 0x3d0 = sp + 0x3c0 + 16 by omega, rc 16 (by omega)]; exact r3d0,
    by rw [show sp + 0x3c0 = sp + 0x3c0 + 0 by omega, rc 0 (by omega)]; exact r3c0,
    by rw [rs 0x398 (by simp only [KeptJ]; omega)]; exact r398, by rw [rs 0x390 (by simp only [KeptJ]; omega)]; exact r390,
    by rw [show sp + 0x3d8 = sp + 0x3c0 + 24 by omega, rc 24 (by omega)]; exact r3d8,
    by rw [rs 0x370 (by simp only [KeptJ]; omega)]; exact r370, by rw [rs 0x138 (by simp only [KeptJ]; omega)]; exact r138⟩
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
    exact ⟨⟨c1, c2, by rw [hacc]; exact c3, c4, hx'.held c5, c6, c7, c8⟩, b2, obj_keep hk hl0' b3, b4, b5⟩
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
/-- `Keeps` from a step's frames: `MemFrame` over `R.rt ++ ws`, `LiveFrame` exempting `ws'`, both lists outside every
context object, the kept slots and the guard / TLS words -/
theorem keeps_of {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp K st l0 : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    {ws ws' : List (Nat × Nat)} (hce : CallW.CEnv R L g fs (sp - 8) K 968 M) (hx : LiveExt R L L')
    (hF : MemFrame M M' (R.rt ++ ws)) (hL : LiveFrame M M' L ws') (hreg : M'.regions = M.regions)
    (hwa : ∀ r ∈ ws, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true) (hg : Outside (g + 16) 8 ws)
    (hfw : Outside (fs - 8) 8 ws)
    (hobj : ∀ a k, Obj R L sp K st l0 ex M a k → Outside a k ws ∧ Outside a k ws')
    (hsl : ∀ j, KeptJ j → Outside (sp + j) 8 ws)
    (hsok : StkOK M' R L' st) (hlen : stLen M st ≤ stLen M' st)
    (hst : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hcp : 0 < stCap M st → 0 < stCap M' st) (hai : ArrIn L' st M M') :
    Keeps R L L' g fs sp K st l0 ex M M' := by
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have hce1 := CallW.CEnv.frame hce hF hreg hwa hg hfw
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, d1, d2, d3, d4, d5, d6⟩ := hce1
  refine ⟨hx, fun a k w => hF.accessible a k w,
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hx.liveSep c11 ?_, c12, c13, d1, d2, d3, d4, d5, d6⟩,
    fun a k ho => ?_, fun j hj => ?_, ?_, ?_, hsok, hlen, hst, hcp, hai⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp - 8 + 968 - (sp - 8 - K) = K + 968 by omega]; exact hrt
  · obtain ⟨o1, o2⟩ := hobj a k ho
    rcases ho.1 with h | h
    · exact hL.readLE a k h o2
    · exact hF.readLE a k (by rw [outside_append]; exact ⟨h, o1⟩)
  · have hj' := hj; simp only [KeptJ] at hj'
    exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hrt.of_sub (by omega) (by omega), hsl j hj⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hg⟩)
  · exact hF.readLE _ _ (by rw [outside_append]; exact ⟨f5, hfw⟩)

end FvModexp.Amd64.W4Pro
