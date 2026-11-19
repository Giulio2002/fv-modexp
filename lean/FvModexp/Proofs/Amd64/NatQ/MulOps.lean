import FvModexp.Proofs.Amd64.NatQ.MulRel

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulOps.lean — TIGHT COSTS] The mul SCC (amd64): moving a precondition one frame down

Every inner call of the SCC is made from a frame of `f` bytes below the caller's `RSP`, with memory changed only in
the caller's window. These lemmas move the pieces of `MPre` there: `callEnv_shift` (`CallEnv`, incl. the amd64 TLS
facts; `fsBase` kept), `stkPre_shift` (with the TLS apartness), `Ops.mono` / `Ops.swap` / `Ops.ext` / `Ops.move`.
(`globals_frame`: Amd64/NatQ/SqrKPre.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep stkOK_frame)

/-- the callee's window lies inside the caller's -/
theorem win_sub {s S1 : State} {W ab f stk1 above1 : Nat} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f)
    (hk : f + stk1 ≤ W) (ha : above1 ≤ f + ab) (hW : W ≤ (s.regs 4).toNat) :
    ∀ a n, Outside a n (win s W ab) → Outside a n (win S1 stk1 above1) := by
  intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega

theorem callEnv_shift {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ win s W ab))
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 ≤ f + ab) (hf8 : f % 8 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgr' : S1.mem.readLE ((S1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  have htls : S1.mem.readLE (S1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨htrt, by omega⟩)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF1.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF1.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro hF1 (by
      intro r hr _; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · rw [hg]; exact hgr
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega
  · rw [hfs]; exact htb
  · rw [hfs, hF1.accessible]; exact htr
  · rw [htls, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

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
    (hF : MemFrame s.mem m' (R.rt ++ win s W ab)) (hLF : LiveFrame s.mem m' L []) :
    stW m' st = stW s.mem st ∧ stLen m' st = stLen s.mem st ∧ stCap m' st = stCap s.mem st := by
  have e : ∀ k, k + 8 ≤ 24 → m'.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk =>
    Held.readLE (hok.2.1.sub (by omega) (by omega)) hF ⟨fun a n hin _ => hLF.readLE a n hin trivial⟩
      (hstw.of_sub (by omega) (by omega))
  have e0 := e 0 (by omega); simp only [Nat.add_zero] at e0
  exact ⟨e0, e 8 (by omega), e 16 (by omega)⟩

theorem stkPre_shift {R : RtInv} {L : List (Nat × Nat)} {s S1 : State} {W ab W1 ab1 st : Nat}
    (h : StkPre R L s W ab st) (hF : MemFrame s.mem S1.mem (R.rt ++ win s W ab)) (hLF : LiveFrame s.mem S1.mem L [])
    (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hsub : ∀ a n, Outside a n (win s W ab) → Outside a n (win S1 W1 ab1)) :
    StkPre R L S1 W1 ab1 st := by
  obtain ⟨h0, hok, hstw, hstg, harr, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA, hsttl, hsatl, hftl⟩ := h
  obtain ⟨eW, eL, eC⟩ := hdr_keep hok hstw hF hLF
  have hok' := stkOK_move hok eW eL eC hF.accessible
  have hfP : BasicSqr.freeP S1.mem st = BasicSqr.freeP s.mem st := by
    simp only [BasicSqr.freeP]; rw [eW, eL]
  have hfN : BasicSqr.freeN S1.mem st = BasicSqr.freeN s.mem st := by
    simp only [BasicSqr.freeN]; rw [eC, eL]
  have hgd : NatSqr.guard S1 = NatSqr.guard s := by simp only [NatSqr.guard]; rw [hg]
  have htd : NatSqr.tls S1 = NatSqr.tls s := by simp only [NatSqr.tls]; rw [hfs]
  refine ⟨h0, hok', hsub _ _ hstw, by rw [hgd]; exact hstg, ?_, by rw [hfP, hfN, hgd]; exact hfg,
    by rw [hfP, hfN]; exact hsub _ _ hfw, by rw [hfP, hfN]; exact hsf, hswb, by rw [hfP, hfN]; exact hfh, hsgA,
    by rw [hfP, hfN]; exact hfgA, by rw [htd]; exact hsttl, ?_, by rw [hfP, hfN, htd]; exact hftl⟩
  · rw [eW, eC, hgd]; intro hc; obtain ⟨q1, q2⟩ := harr hc; exact ⟨hsub _ _ q1, q2⟩
  · rw [eW, eC, htd]; exact hsatl

/-! ## The operand facts -/

section
variable {R : RtInv} {L : List (Nat × Nat)} {m : Memory} {g t : Nat} {ws : List (Nat × Nat)}
  {st zp zc xp xl xc yp yl yc : Nat}

theorem Ops.mono {ws' : List (Nat × Nat)} (h : Ops R L m g t ws st zp zc xp xl xc yp yl yc)
    (hs : ∀ a n, Outside a n ws → Outside a n ws') : Ops R L m g t ws' st zp zc xp xl xc yp yl yc := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨y1, y2, y3, y4, y5, y6⟩, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  exact ⟨⟨x1, x2, x3, x4, x5, fun h => ⟨hs _ _ (x6 h).1, (x6 h).2⟩⟩,
    ⟨y1, y2, y3, y4, y5, fun h => ⟨hs _ _ (y6 h).1, (y6 h).2⟩⟩, ⟨z1, z2, hs _ _ z3, z4, z5, z6⟩, hl⟩

theorem Ops.swap (h : Ops R L m g t ws st zp zc xp xl xc yp yl yc) : Ops R L m g t ws st zp zc yp yl yc xp xl xc := by
  obtain ⟨hx, hy, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  exact ⟨hy, hx, ⟨z1, z2, z3, z4, z6, z5⟩, by omega⟩

theorem Ops.ext {L1 : List (Nat × Nat)} (h : Ops R L m g t ws st zp zc xp xl xc yp yl yc) (he : LiveExt R L L1) :
    Ops R L1 m g t ws st zp zc xp xl xc yp yl yc := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨y1, y2, y3, y4, y5, y6⟩, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  refine ⟨⟨x1, x2, x3, x4, fun h => ⟨he.held (x5 h).1, (x5 h).2⟩, x6⟩,
    ⟨y1, y2, y3, y4, fun h => ⟨he.held (y5 h).1, (y5 h).2⟩, y6⟩, ⟨z1, ?_, z3, z4, z5, z6⟩, hl⟩
  intro hc; obtain ⟨q1, q2, q3, q4⟩ := z2 hc; exact ⟨q1, he.held q2, q3, q4⟩

/-- through a memory change that keeps the stack header and accessibility -/
theorem Ops.move {m' : Memory} (h : Ops R L m g t ws st zp zc xp xl xc yp yl yc)
    (eW : stW m' st = stW m st) (eL : stLen m' st = stLen m st) (eC : stCap m' st = stCap m st)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) :
    Ops R L m' g t ws st zp zc xp xl xc yp yl yc := by
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

end FvModexp.Amd64.Q.NatMul
