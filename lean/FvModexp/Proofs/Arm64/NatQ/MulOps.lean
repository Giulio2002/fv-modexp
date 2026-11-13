import FvModexp.Proofs.Arm64.NatQ.MulRel

/-!
# [Q-form copy of Arm64/Nat/MulOps.lean — TIGHT COSTS, divmc s34] The mul SCC (arm64): moving a precondition one frame down

Every inner call of the SCC (the swap, the chunk products, `karatsuba`'s `(*Int).mul`, `(*Int).mul`'s `nat.mul`) is
made from a frame of `f` bytes below the caller's `SP`, with memory changed only in the caller's window. These lemmas
move the pieces of `MPre` there: `callEnv_shift` (`CallEnv`), `globals_shift`, `stkPre_shift`, `Ops.mono` /
`Ops.frame` / `Ops.ext` / `Ops.swap`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.RunIface (Globals)
open FvModexp.Arm64.Q.NatSqr (StkPre StkSep stkOK_frame)

/-- the callee's window lies inside the caller's -/
theorem win_sub {s S1 : State} {W ab f stk1 above1 : Nat} (hsp : S1.sp.toNat = s.sp.toNat - f)
    (hk : f + stk1 ≤ W) (ha : above1 + 8 ≤ f) (hW : W ≤ s.sp.toNat) :
    ∀ a n, Outside a n (win s W ab) → Outside a n (win S1 stk1 above1) := by
  intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega

theorem callEnv_shift {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W ab))
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hg : S1.regs 28 = s.regs 28) (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 + 8 ≤ f) (hab : 8 ≤ ab) (hf16 : f % 16 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  unfold Apart at hga
  have hgr' : S1.mem.readLE ((S1.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hF1.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hF1.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact dataLoaded_win hdl hreg hro hF1 hw (by
      intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega

theorem globals_shift {R : RtInv} {m m' : Memory} {ws ws' rs : List (Nat × Nat)}
    (h : Globals R m ws) (hF : MemFrame m m' (R.rt ++ rs)) (hrs : ∀ a n, Outside a n ws → Outside a n rs)
    (hws : ∀ a n, Outside a n ws → Outside a n ws') : Globals R m' ws' := by
  obtain ⟨h40, h12, h80, h40d, e1, e2, e3, hacc, hrt, hw, hwacc, hwrt, hww⟩ := h
  have hg : Outside RunIface.gA 32 (R.rt ++ rs) := by rw [outside_append]; exact ⟨hrt, hrs _ _ hw⟩
  have hgw : Outside StackNat.wbA 4 (R.rt ++ rs) := by rw [outside_append]; exact ⟨hwrt, hrs _ _ hww⟩
  have eg : RunIface.gA = 7147136 := rfl
  have e4 : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
      RunIface.gA := by rw [eg]; rfl
  refine ⟨?_, ?_, ?_, ?_, e1, e2, e3, by rw [hF.accessible]; exact hacc, hrt, hws _ _ hw,
    by rw [hF.accessible]; exact hwacc, hwrt, hws _ _ hww⟩
  · rw [e1, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e1]; exact h40
  · rw [e2, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e2]; exact h12
  · rw [e3, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e3]; exact h80
  · rw [e4, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e4]; exact h40d

/-- the stack header keeps its words through a frame that misses it -/
theorem hdr_frame {m m' : Memory} {rs : List (Nat × Nat)} {st : Nat} (hF : MemFrame m m' rs)
    (ho : Outside st 24 rs) : stW m' st = stW m st ∧ stLen m' st = stLen m st ∧ stCap m' st = stCap m st := by
  refine ⟨hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega)), hF.readLE _ _ (ho.of_sub (by omega) (by omega)),
    hF.readLE _ _ (ho.of_sub (by omega) (by omega))⟩

theorem stkOK_move {R : RtInv} {L : List (Nat × Nat)} {m m' : Memory} {st : Nat} (h : StkOK m R L st)
    (eW : stW m' st = stW m st) (eL : stLen m' st = stLen m st) (eC : stCap m' st = stCap m st)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : StkOK m' R L st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, by rw [hacc]; exact h3, h4, ?_, by rw [eL, eC]; exact h6, by rw [eC]; exact h7⟩
  rw [eW, eC]; intro hc; obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, q2, by rw [hacc]; exact q3, q4⟩

/-- the stack header through a window-and-runtime frame (it is held and outside the window) -/
theorem hdr_keep {R : RtInv} {L : List (Nat × Nat)} {s : State} {W ab st : Nat} {m' : Memory}
    (hok : StkOK s.mem R L st) (hstw : Outside st 24 (win s W ab))
    (hF : MemFrame s.mem m' (R.rt ++ winA s W ab)) (hLF : LiveFrame s.mem m' L []) :
    stW m' st = stW s.mem st ∧ stLen m' st = stLen s.mem st ∧ stCap m' st = stCap s.mem st := by
  have e : ∀ k, k + 8 ≤ 24 → m'.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk =>
    Held.readLE (hok.2.1.sub (by omega) (by omega)) hF ⟨fun a n hin _ => hLF.readLE a n hin trivial⟩
      ((winA_of_win' hstw).of_sub (by omega) (by omega))
  have e0 := e 0 (by omega); simp only [Nat.add_zero] at e0
  exact ⟨e0, e 8 (by omega), e 16 (by omega)⟩

theorem stkPre_shift {R : RtInv} {L : List (Nat × Nat)} {s S1 : State} {W ab W1 ab1 st : Nat}
    (h : StkPre R L s W ab st) (hF : MemFrame s.mem S1.mem (R.rt ++ winA s W ab)) (hLF : LiveFrame s.mem S1.mem L [])
    (hg : S1.regs 28 = s.regs 28) (hsub : ∀ a n, Outside a n (win s W ab) → Outside a n (win S1 W1 ab1)) :
    StkPre R L S1 W1 ab1 st := by
  obtain ⟨h0, hok, hstw, hstg, harr, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩ := h
  obtain ⟨eW, eL, eC⟩ := hdr_keep hok hstw hF hLF
  have hok' := stkOK_move hok eW eL eC hF.accessible
  have hfP : BasicSqr.freeP S1.mem st = BasicSqr.freeP s.mem st := by
    simp only [BasicSqr.freeP]; rw [eW, eL]
  have hfN : BasicSqr.freeN S1.mem st = BasicSqr.freeN s.mem st := by
    simp only [BasicSqr.freeN]; rw [eC, eL]
  have hgd : NatSqr.guard S1 = NatSqr.guard s := by simp only [NatSqr.guard]; rw [hg]
  refine ⟨h0, hok', hsub _ _ hstw, by rw [hgd]; exact hstg, ?_, by rw [hfP, hfN, hgd]; exact hfg,
    by rw [hfP, hfN]; exact hsub _ _ hfw, by rw [hfP, hfN]; exact hsf, hswb, by rw [hfP, hfN]; exact hfh, hsgA,
    by rw [hfP, hfN]; exact hfgA⟩
  rw [eW, eC, hgd]; intro hc; obtain ⟨q1, q2⟩ := harr hc; exact ⟨hsub _ _ q1, q2⟩

/-! ## The operand facts -/

section
variable {R : RtInv} {L : List (Nat × Nat)} {m : Memory} {g : Nat} {ws : List (Nat × Nat)}
  {st zp zc xp xl xc yp yl yc : Nat}

theorem Ops.mono {ws' : List (Nat × Nat)} (h : Ops R L m g ws st zp zc xp xl xc yp yl yc)
    (hs : ∀ a n, Outside a n ws → Outside a n ws') : Ops R L m g ws' st zp zc xp xl xc yp yl yc := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨y1, y2, y3, y4, y5, y6⟩, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  exact ⟨⟨x1, x2, x3, x4, x5, fun h => ⟨hs _ _ (x6 h).1, (x6 h).2⟩⟩,
    ⟨y1, y2, y3, y4, y5, fun h => ⟨hs _ _ (y6 h).1, (y6 h).2⟩⟩, ⟨z1, z2, hs _ _ z3, z4, z5, z6⟩, hl⟩

theorem Ops.swap (h : Ops R L m g ws st zp zc xp xl xc yp yl yc) : Ops R L m g ws st zp zc yp yl yc xp xl xc := by
  obtain ⟨hx, hy, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  exact ⟨hy, hx, ⟨z1, z2, z3, z4, z6, z5⟩, by omega⟩

theorem Ops.ext {L1 : List (Nat × Nat)} (h : Ops R L m g ws st zp zc xp xl xc yp yl yc) (he : LiveExt R L L1) :
    Ops R L1 m g ws st zp zc xp xl xc yp yl yc := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨y1, y2, y3, y4, y5, y6⟩, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  refine ⟨⟨x1, x2, x3, x4, fun h => ⟨he.held (x5 h).1, (x5 h).2⟩, x6⟩,
    ⟨y1, y2, y3, y4, fun h => ⟨he.held (y5 h).1, (y5 h).2⟩, y6⟩, ⟨z1, ?_, z3, z4, z5, z6⟩, hl⟩
  intro hc; obtain ⟨q1, q2, q3, q4⟩ := z2 hc; exact ⟨q1, he.held q2, q3, q4⟩

/-- through a memory change that keeps the stack header and accessibility -/
theorem Ops.move {m' : Memory} (h : Ops R L m g ws st zp zc xp xl xc yp yl yc)
    (eW : stW m' st = stW m st) (eL : stLen m' st = stLen m st) (eC : stCap m' st = stCap m st)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) :
    Ops R L m' g ws st zp zc xp xl xc yp yl yc := by
  have hfP : BasicSqr.freeP m' st = BasicSqr.freeP m st := by simp only [BasicSqr.freeP]; rw [eW, eL]
  have hfN : BasicSqr.freeN m' st = BasicSqr.freeN m st := by simp only [BasicSqr.freeN]; rw [eC, eL]
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨y1, y2, y3, y4, y5, y6⟩, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  refine ⟨⟨x1, x2, x3, by rw [hacc]; exact x4, x5, ?_⟩, ⟨y1, y2, y3, by rw [hacc]; exact y4, y5, ?_⟩,
    ⟨z1, ?_, z3, ?_, z5, z6⟩, by rw [eL]; exact hl⟩
  · simp only [StkSep, hfP, hfN]; exact x6
  · simp only [StkSep, hfP, hfN]; exact y6
  · intro hc; obtain ⟨q1, q2, q3, q4⟩ := z2 hc; exact ⟨q1, q2, by rw [hacc]; exact q3, q4⟩
  · simp only [StkSep, hfP, hfN]; exact z4

end

end FvModexp.Arm64.Q.NatMul
