import FvModexp.Proofs.Amd64.Exp.W4EnDefs
import FvModexp.Proofs.Amd64.Exp.W4XnK

set_option autoImplicit false

/-!
# window-4 entry (amd64): the entry facts `EPre` and `W4Pro.CtxX` at `xnE` (agent expmc s57; twin of
`Arm64.W4EnPre` + `Arm64.W4EnCtx`)

At the entry state `s` (`RSP = sp + 0x388`, the function's frame is `sp`), register arguments `z = (zp, _, zc)`
`AX, BX, CX`, `stk = st` `DI`, `x = (xp, xl, xc)` `SI, R8, R9`; stack arguments `y = (yp, ylen, _)` at `sp + 0x390`,
`m = (mp, n, mc)` at `sp + 0x3a8`. The window is `[sp - 8 - K, sp + 0x3f8)` (callee stacks, frame, saved `BP`,
return address, stack arguments, register spill area); `l0 = len + rnd(23n)` is the stack level after the inline
`stk.reserve(23n)`. `ctxX_of` builds `CtxX` (with `x[0:n] := m` — `CtxX`'s `x` fields are not used before `toSn1`
re-spills the normalised `x`) from `EPre` and the frames of the entry segment.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4En

/-- `[a, a + k)` inside `[A, A + n)`, which an unfolded `Apart B m A n` keeps apart from `[B, B + m)`: the omega side
conditions then need no case split on the context's disjunctions -/
theorem in_or {B m A n a k : Nat} (h : B + m ≤ A ∨ A + n ≤ B) (h1 : A ≤ a) (h2 : a + k ≤ A + n) :
    a + k ≤ B ∨ B + m ≤ a := by omega

open FvModexp.Amd64.W4Pro (Obj AW stUp)

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an operand object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - 8 - K) (K + 0x400) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the entry facts of window-4 -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (g fs sp st bp r zp zc xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - 8 - K, sp + 0x3f8)] ∧ Outside wTy 16 R.rt ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  OE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  OE R L sp K st s.mem yp (8 * ylen) ∧ s.mem.accessible yp (8 * ylen) false = true ∧ yp + 8 * ylen ≤ 2 ^ 48 ∧
    NatNorm s.mem yp ylen ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  OE R L sp K st s.mem xp (8 * xc) ∧ s.mem.accessible xp (8 * xc) false = true ∧ xp + 8 * xc ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ 0 < xl ∧ xl ≤ 128 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (2 * n ≤ zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart (fs - 8) 8 zp (8 * zc) ∧ Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - 8 - K) (K + 0x400) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x400) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  Apart st 24 StackNat.wbA 4 ∧ Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  (s.regs 5).toNat = bp ∧ s.mem.readLE (sp + 0x388) 8 = r ∧ r < 2 ^ 47 ∧
  s.mem.readLE (sp + 0x390) 8 = yp ∧ s.mem.readLE (sp + 0x398) 8 = ylen ∧ s.mem.readLE (sp + 0x3a8) 8 = mp ∧
  s.mem.readLE (sp + 0x3b0) 8 = n ∧ s.mem.readLE (sp + 0x3b8) 8 = mc ∧
  R.inv b L g (view R.rt L s.mem)

/-- the array after the reserve: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

set_option maxRecDepth 20000 in
/-- an entry object is an `Obj` of the context at `xnE` (live set `L1 ⊇ L`, level `l0 ≥ len`) -/
theorem obj_of_OE {R : RtInv} {L L1 : List (Nat × Nat)} {sp K st l0 a k : Nat} {M0 M : Memory}
    (h : OE R L sp K st M0 a k) (hx : LiveExt R L L1) (hkf : ArrKF R L st M0 M)
    (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stCap M st) :
    Obj R L1 sp K st l0 [] M a k := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hx.held h1, by simp only [AW]; unfold Apart at h2 ⊢; omega, h3, ?_, fun e he => by simp at he⟩
  rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · simp only [stUp, free, Apart] at h4 ⊢; rw [e1, e2]; rw [e2] at hl'; omega
  · have := W4Pro.apart_fresh hin hap h1
    simp only [stUp]; unfold Apart at this ⊢; omega

/-- an entry object keeps its bytes -/
theorem rd_of_OE {R : RtInv} {L : List (Nat × Nat)} {sp K st a k : Nat} {M0 M : Memory}
    (h : OE R L sp K st M0 a k) (hF : MemFrame M0 M (R.rt ++ [(sp - 8 - K, sp + 0x3f8), (st, st + 24)]))
    (hLF : LiveFrame M0 M L [(st, st + 24)]) {a' k' : Nat} (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) :
    M.readLE a' k' = M0.readLE a' k' := by
  obtain ⟨hh, hw, hs, -⟩ := h
  unfold Apart at hw hs
  rcases hh with hL | hO
  · exact hLF.readLE a' k' (hL.sub h1 h2) (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine hF.readLE a' k' ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hO.of_sub h1 h2, by omega, by omega⟩

theorem liveSep_sub' {L : List (Nat × Nat)} {lo hi lo' hi' : Nat} (h : LiveSep L [(lo, hi)]) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : LiveSep L [(lo', hi')] := by
  intro r hr
  have := h r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- the CallW environment at `xnE` (window `[sp - 8 - K, sp + 0x3f8)`) from the entry one and the entry frame -/
theorem cenv_at {R : RtInv} {L L1 : List (Nat × Nat)} {g fs sp K st : Nat} {M0 M : Memory}
    (h : CallW.CEnv R L g fs (sp - 8) K 0x400 M0)
    (hF : MemFrame M0 M (R.rt ++ [(sp - 8 - K, sp + 0x3f8), (st, st + 24)])) (hrg : M.regions = M0.regions)
    (hx : LiveExt R L L1) (hsta : M0.accessible st 24 true = true) (hstg : Apart st 24 (g + 16) 8)
    (hstf : Apart st 24 (fs - 8) 8) : CallW.CEnv R L1 g fs (sp - 8) K 0x400 M := by
  have h' := h
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h'
  unfold Apart at hga f6 hstg hstf
  have := CallW.CEnv.frame h hF hrg (fun r hr _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hacc
      · simp only; rw [show st + 24 - st = 24 by omega]; exact hsta)
    (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, a12, a13, a14, a15, a16, a17, a18, a19⟩ := this
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hx.liveSep hLs fun r hr => ?_, a12, a13, a14, a15, a16, a17,
    a18, a19⟩
  simp only [List.mem_singleton] at hr; subst hr; simp only
  rw [show sp - 8 + 0x400 - (sp - 8 - K) = K + 0x400 by omega]; exact hrt

/-- window-4's loop environment from the CallW one -/
theorem env_of {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs (sp - 8) K 0x400 M) (hal : sp % 8 = 0) (hK : 4288 ≤ K)
    (hadx : M.accessible MontHyp.hasADX 1 false = true) : W4Loop.Env R L g fs sp M := by
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  unfold Apart at hga f6
  exact ⟨hal, by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega), hg1, hg2,
    by omega, hrt.of_sub (by omega) (by omega), by unfold Apart; omega, hgrt, liveSep_sub' hLs (by omega) (by omega),
    ⟨f1, f2⟩, f3, f4, by unfold Apart; omega, f5, hadx⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `CtxX` at `xnE` from the entry facts and the frames of the entry segment (entry memory `s.mem`, `xnE` memory `M`) -/
theorem ctxX_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc s) (hstnz : st ≠ 0)
    {M : Memory} {L1 : List (Nat × Nat)} (hF : MemFrame s.mem M (R.rt ++ [(sp - 8 - K, sp + 0x3f8), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hkf : ArrKF R L st s.mem M) (hlen : stLen M st = stLen s.mem st + StackNat.rnd (23 * n))
    (hcap : stLen M st ≤ stCap M st) (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hsl : ESl M sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st)) :
    W4Pro.CtxX R L1 g fs sp K n mp mc (s.mem.readLE mp (8 * n)) mp (s.mem.readLE mp (8 * n)) yp ylen
      (s.mem.readLE yp (8 * ylen)) (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen M st)
      bp r [] M ∧
    Obj R L1 sp K st (stLen M st) [] M (sp + 0x3e0) 0x18 ∧ M.accessible (sp + 0x3c0) 0x38 false = true ∧
    W4Pro.XIn R L1 sp K st (stLen M st) M xp xl xc ∧ NatNorm M xp xl ∧
    M.readLE xp (8 * xl) = s.mem.readLE xp (8 * xl) := by
  obtain ⟨he, hgl, hwt, hadx, hn, hn128, hmc, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl',
    hxO, hxa, hx48, hxN, hxl, hxl', hxlc, hxc, hzp, hzc, hz, hgO, hsok, hstw, hstg, hstfs, harr, hwbA, hstf, hl16,
    hbp, hr388, hr47, r390, r398, r3a8, r3b0, r3b8, hinv⟩ := hP
  obtain ⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, hce0, hsv⟩ := he
  have hce0' := hce0
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0'
  unfold Apart at hstw hstg hstfs hga f6
  have hl0 : stLen s.mem st ≤ stLen M st := by omega
  have hsok' := hsok
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok'
  have hce := cenv_at hce0 hF hrg hx k3 (by unfold Apart; omega) (by unfold Apart; omega)
  have hacc' : ∀ a k w, M.accessible a k w = s.mem.accessible a k w := fun a k w => hF.accessible a k w
  have obj := fun {a k : Nat} (h : OE R L sp K st s.mem a k) => obj_of_OE h hx hkf hl0 hcap
  have rd := fun {a k a' k' : Nat} (h : OE R L sp K st s.mem a k) (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) =>
    rd_of_OE (a' := a') (k' := k') h hF hLF h1 h2
  have hrn : 0 < StackNat.rnd (23 * n) := rnd23_pos n hn
  have hcap0 : 0 < stCap M st := by omega
  have hsthL : InRanges st 24 L1 ∨ Outside st 24 R.rt := hx.held k2
  have inp := fun {a k : Nat} (h : OE R L sp K st s.mem a k) (ha : s.mem.accessible a k false = true)
      (h48 : a + k ≤ 2 ^ 48) => (⟨by rw [hacc']; exact ha, h48, hx.held h.1,
        by have := h.2.1; unfold Apart at this ⊢; omega⟩ :
        M.accessible a k false = true ∧ a + k ≤ 2 ^ 48 ∧ (InRanges a k L1 ∨ Outside a k R.rt) ∧
          Apart a k (sp - 4296) (4296 + 0x3c0))
  -- the array after the reserve
  have harr' : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 8 - K) (K + 0x400) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧ Apart (stW M st) (8 * stCap M st) (fs - 8) 8 := by
    intro hc
    rcases hkf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e1, e2]; rw [e2] at hc; exact harr hc
    · have h1 := W4Pro.out_inR hrt hin
      have h2 := W4Pro.out_inR hgrt hin
      have h3 := W4Pro.out_inR f5 hin
      unfold Apart; omega
  have hup := harr' hcap0
  unfold Apart at hup
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17⟩ := hsl
  refine ⟨⟨env_of hce hal (by omega) (by rw [hacc']; exact hadx), CallW.CEnv.mono hce (Nat.le_refl _) (by omega),
    hK, hK20, hn, hn128, hmc, hmc', inp hmO hma hm48, obj hmO, rd hmO (Nat.le_refl _) (Nat.le_refl _), ?mN,
    inp hmO hma hm48, obj hmO, rd hmO (Nat.le_refl _) (Nat.le_refl _),
    inp hyO hya hy48, obj hyO, rd hyO (Nat.le_refl _) (Nat.le_refl _), ?yi, ?yi0, hyl, hyl', hzc, ?z, ?fin,
    hsthL, by simp only [AW]; unfold Apart; omega, ⟨k1, hsthL, by rw [hacc']; exact k3, k4, hnl, hcap, hc40⟩,
    by omega, Nat.le_refl _, hcap0, ?arr, ?ug, ?uf, ?uw, ?su, hstg, hstfs,
    ?glob, obj hgO, hwbA, ?wbacc, ?sacc, hrt.of_sub (by omega) (by omega), ?sobj, q15, q16, q17, q8, q7, q14, q13, q9,
    hstnz⟩, ?sobj2, ?sacc2, ⟨hxlc, by omega, hxc, by rw [hacc']; exact hxa, hx48, obj hxO⟩, ?xN,
    rd hxO (Nat.le_refl _) (by omega)⟩
  case sobj2 =>
    refine ⟨Or.inr (hrt.of_sub (by omega) (by omega)), by simp only [AW]; unfold Apart; omega,
      by unfold Apart; exact in_or hstw (by omega) (by omega), by simp only [stUp, Apart]; omega,
      fun e he => by simp at he⟩
  case sacc2 =>
    rw [hacc']; exact Janus.Arm64.Memory.accessible_weaken _
      (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
  case xN =>
    rcases hxN with h | h
    · exact Or.inl h
    · right; rw [rd hxO (by omega) (by omega)]; exact h
  case mN =>
    rcases hmN with h | h
    · exact Or.inl h
    · right; rw [rd hmO (by omega) (by omega)]; exact h
  case yi => rw [rd hyO (by omega) (by omega)]
  case yi0 =>
    rcases hyN with h | h
    · omega
    · exact Nat.pos_of_ne_zero h
  case z =>
    intro h2
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hz h2
    refine ⟨⟨h2, hzc, by rw [hacc']; exact b2, b3, hx.held b1.1, by have := b1.2.1; unfold Apart at this ⊢; omega,
      b5, b6⟩, b4, obj b1, b7, b8⟩
  case fin =>
    refine ⟨hal, by omega, by omega, by rw [hacc']; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega),
      q3, q4, q5, q6, k4, by rw [hacc']; exact k3, ?_, by unfold Apart; omega, q1, q2, hr47⟩
    simp only [stLen, stCap] at hcap hlen ⊢; omega
  case arr =>
    intro hc
    obtain ⟨a1, a2, a3⟩ := harr' hc
    refine ⟨?_, a2, a3⟩
    simp only [AW]; unfold Apart at a1 ⊢; omega
  case ug => simp only [stUp, Apart]; omega
  case uf => simp only [stUp, Apart]; omega
  case uw => simp only [stUp, AW, Apart]; omega
  case su =>
    rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [free, Apart] at hstf; simp only [stUp, Apart]; rw [e1, e2]; rw [e2] at hcap; omega
    · have := W4Pro.apart_fresh hin hap k2
      simp only [stUp]; unfold Apart at this ⊢; omega
  case glob =>
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hgl
    have hrdG : ∀ j, j + 8 ≤ 32 → M.readLE (RunIface.gA + j) 8 = s.mem.readLE (RunIface.gA + j) 8 :=
      fun j hj => rd hgO (by omega) (by omega)
    simp only [outside_cons, outside_nil, and_true] at g10 g13
    have o1 : Outside RunIface.gA 32 [(sp - 8 - K, sp + 0x3c0)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    have o2 : Outside RunIface.wbA 4 [(sp - 8 - K, sp + 0x3c0)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hacc']; exact g8, g9, o1, by rw [hacc']; exact g11, g12, o2⟩
    · rw [g5, hrdG 8 (by omega), ← g5]; exact g1
    · rw [g6, hrdG 16 (by omega), ← g6]; exact g2
    · rw [g7, hrdG 24 (by omega), ← g7]; exact g3
    · have := hrdG 0 (by omega); simp only [Nat.add_zero] at this
      show M.readLE RunIface.gA 8 = 40; rw [this]; exact g4
  case wbacc => rw [hacc']; exact hgl.2.2.2.2.2.2.2.2.2.2.1
  case sacc =>
    rw [hacc']; exact Janus.Arm64.Memory.accessible_weaken _
      (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
  case sobj =>
    refine ⟨Or.inr (hrt.of_sub (by omega) (by omega)), by simp only [AW]; unfold Apart; omega,
      by unfold Apart; exact in_or hstw (by omega) (by omega), by simp only [stUp, Apart]; omega,
      fun e he => by simp at he⟩

end FvModexp.Amd64.W4En
