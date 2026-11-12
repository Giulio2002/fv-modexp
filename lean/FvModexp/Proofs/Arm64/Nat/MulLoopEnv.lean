import FvModexp.Proofs.Arm64.Nat.MulLoopRel

/-!
# `nat.mul` (arm64), chunk loop: the environment of an inner call from `LB`

`LB.dl` (read-only data), `LB.grd` (stack guard), `LB.callee` (`CallEnv` at `SP - 256`), `LB.stk` / `LB.stkPre`
(`StkPre` at an inner call), `LB.glob` (threshold globals), `LB.sep` (an operand range kept `StkSep` at `Mi`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

/-- the frame from the entry to `Mi` (the result range dropped when it is fresh, i.e. inside `R.rt`) -/
theorem LB.frE (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    MemFrame s.mem Mi (R.rt ++ winA s W 88 ++ lws s.mem st p (xl + yl)) := by
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have e : lws M st p (xl + yl) = lws s.mem st p (xl + yl) := by simp only [lws, stkWs]; rw [eW, eL, eC]
  rw [← e]
  exact h.core.F.trans h.fr fun a n ho => ⟨by simp only [outside_append] at ho ⊢; exact ⟨ho.1.1, ho.1.2⟩, ho⟩

/-- the read-only data stays loaded -/
theorem LB.dl (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    Extracted.program.DataLoaded Mi := by
  obtain ⟨⟨-, ⟨hal, hb, ha', hw⟩, hdl, -, -, -, -, hro⟩, -⟩ := h.core.pre
  have hzlive : NatLive s.mem R L zp zc := h.core.pre.2.2.2.2.2.1.2.2.1.2.1
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, -, hsacc, -, hnl, hlc, -⟩, -⟩ := hsp
  have hcap := h.core.cap
  rcases h.core.kind with ⟨hpz, hcz⟩ | ⟨hin, -, -⟩
  · rw [← hpz, ← hcz] at hzlive
    have hfr : MemFrame s.mem Mi (R.rt ++ (winA s W 88 ++ lws s.mem st p (xl + yl))) := by
      rw [← List.append_assoc]; exact h.frE
    refine dataLoaded_frame hdl h.reg hro hfr fun r hr hlt => ?_
    simp only [winA, lws, stkWs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl | rfl | rfl
    · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · obtain ⟨-, -, hacc, -⟩ := hzlive (by simp only at hlt; omega)
      exact Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)
    · exact Memory.accessible_mono _ hsacc (by simp only; omega) (by simp only; omega)
    · simp only at hlt
      obtain ⟨-, -, hacc, -⟩ := hnl (by omega)
      exact Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)
  · have hfr : MemFrame s.mem Mi (R.rt ++ (winA s W 88 ++ stkWs s.mem st)) := by
      refine h.frE.mono fun a n ho => ?_
      simp only [lws, outside_append, outside_cons] at ho ⊢
      exact ⟨⟨ho.1, ho.2.1⟩, NatSub.outside_of_inRanges ho.1 (hin.sub (Nat.le_refl _) (by omega)), ho.2.2⟩
    refine dataLoaded_frame hdl h.reg hro hfr fun r hr hlt => ?_
    simp only [winA, stkWs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl | rfl
    · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · exact Memory.accessible_mono _ hsacc (by simp only; omega) (by simp only; omega)
    · simp only at hlt
      obtain ⟨-, -, hacc, -⟩ := hnl (by omega)
      exact Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)

/-- the stack-NatSqr.guard word keeps its value -/
theorem LB.grd (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    Mi.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
  obtain ⟨hW, hWs, -, -, hout, hgr, hga, hcap, -⟩ := h.lay
  have h40 := h.h40
  have hpg := h.core.pg (by omega)
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, -, -, hstg, -, hfg, -⟩ := hsp
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hstg hfg
  unfold Apart at hpg hstg hfg hga
  refine h.frE.readLE _ _ ?_
  simp only [winA, lws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨hgr, by omega, by omega⟩, by omega, by omega, by omega⟩

/-- the call environment of a callee at `SP - 256` (window inside ours, `above ≤ 88`) -/
theorem LB.callee (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {S1 : State}
    {stk1 above1 : Nat} (hsp : S1.sp.toNat = s.sp.toNat - 256) (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = Mi)
    (hk : 256 + stk1 ≤ W) (ha : above1 ≤ 88) : CallEnv R Lk S1 stk1 above1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩, -⟩ := h.core.pre
  unfold Apart at hga
  have hgrd := h.grd
  have hLs1 := h.wsep
  obtain ⟨ns, hLk, hn, -⟩ := h.ext
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hm, h.frE.accessible]; exact hg2, by rw [hg, hm, hgrd, hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hm, h.frE.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [hm]; exact h.dl
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]
    rw [hLk] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs1 r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := NatSub.outside_of_inRanges hout (hn r hr).1; omega

/-- the stack's current array and free part: outside the window, apart from the NatSqr.guard word and the header, held -/
theorem LB.stk (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    (0 < stCap Mi st → Outside (stW Mi st) (8 * stCap Mi st) (win s W 88) ∧
      Apart (stW Mi st) (8 * stCap Mi st) (NatSqr.guard s) 8) ∧
    Apart (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) (NatSqr.guard s) 8 ∧
    Outside (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) (win s W 88) ∧
    Apart st 24 (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) ∧ Held R Lk (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) ∧
    Apart (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) RunIface.gA 32 := by
  obtain ⟨hW, hWs, -, -, hout, hgr, hga, -⟩ := h.lay
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  have hgrt : Outside RunIface.gA 32 R.rt := h.core.pre.2.2.2.1.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, hsth, -, -, -, hlc0, -⟩, -, -, hsarr, hfg, hfw, hstf, -, hfh, -, hfgA⟩ := hsp
  have hlc := h.sok.2.2.2.2.2.1
  have hnl := h.sok.2.2.2.2.1
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hfg hfw hstf hfh hsarr hfgA ⊢
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
  · rw [e1, e2, eW, eC] at hnl ⊢; rw [e2, eC] at hlc; rw [eL] at e3
    refine ⟨hsarr, ?_, ?_, ?_, h.ext.held (h.core.ext.held (hfh.sub (by omega) (by omega))), ?_⟩
    · unfold Apart at hfg ⊢; omega
    · exact hfw.of_sub (by omega) (by omega)
    · unfold Apart at hstf ⊢; omega
    · unfold Apart at hfgA ⊢; omega
  · have hgo := NatSub.outside_of_inRanges hgr hin
    have hst := apart_of_held (h.core.ext.held hsth) hin hap
    have hcap : 0 < stCap Mi st := by
      have := h.slen; simp only [rnd] at this; have := h.h40; omega
    obtain ⟨-, hh, -, -⟩ := hnl hcap
    have hw : ∀ a k, stW Mi st ≤ a → a + k ≤ stW Mi st + 8 * stCap Mi st → Outside a k (win s W 88) := by
      intro a k h1 h2
      have := NatSub.outside_of_inRanges (hout.of_sub (a := s.sp.toNat - W) (n := W + 88) (by omega) (by omega)) hin
      simp only [win, outside_cons, outside_nil, and_true]; omega
    refine ⟨fun _ => ⟨hw _ _ (by omega) (by omega), by unfold Apart; omega⟩, by unfold Apart; omega,
      hw _ _ (by omega) (by omega), by unfold Apart at hst ⊢; omega, hh.sub (by omega) (by omega), ?_⟩
    have := NatSub.outside_of_inRanges hgrt hin
    unfold Apart; omega

/-- **`StkPre` at an inner call** (`SP - 256`, window `W' + 256 ≤ W`, above `≤ 88`) -/
theorem LB.stkPre (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {S1 : State} {W' a : Nat}
    (hsp : S1.sp.toNat = s.sp.toNat - 256) (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = Mi)
    (hk : 256 + W' ≤ W) (ha : a ≤ 88) : StkPre R Lk S1 W' a st := by
  obtain ⟨hW, hWs, -⟩ := h.lay
  have hsp' : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨hst0, -, hstw, hstg, -, -, -, -, hstwb, -, hsgA, -⟩ := hsp'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.stk
  have hwin : ∀ x k, Outside x k (win s W 88) → Outside x k (win S1 W' a) := by
    intro x k hx; simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hsp]; omega
  subst hm
  simp only [StkPre, NatSqr.guard, hg] at h1 h2 hstg ⊢
  exact ⟨hst0, h.sok, hwin _ _ hstw, hstg, fun hc => ⟨hwin _ _ (h1 hc).1, (h1 hc).2⟩, h2, hwin _ _ h3, h4, hstwb, h5,
    hsgA, h6⟩

/-- the threshold globals at `Mi` -/
theorem LB.glob (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {w' : List (Nat × Nat)}
    (hw : ∀ x k, Outside x k (win s W 88) → Outside x k w') : RunIface.Globals R Mi w' := by
  have hgl : RunIface.Globals R s.mem (win s W 88) := h.core.pre.2.2.2.1
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  have hpg := h.core.pgA (by have := h.core.cap; have := h.h40; omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsgA, hfgA⟩ := hsp
  have hgw : Outside RunIface.gA 32 (win s W 88) := hgl.2.2.2.2.2.2.2.2.2.1
  have hcap := h.core.cap
  have hfr : MemFrame s.mem Mi (R.rt ++ (winA s W 88 ++ lws s.mem st p (xl + yl))) := by
    rw [← List.append_assoc]; exact h.frE
  refine NatSqr.globals_frame hgl hfr ?_ hw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfgA
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  unfold Apart at hpg hsgA hfgA
  simp only [winA, lws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  omega

/-- an operand range held in `L`, outside the window and `StkSep` at the entry stays readable and `StkSep` at `Mi` -/
theorem LB.sep (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {a n : Nat}
    (hh : Held R L a n) (hs : StkSep s.mem st a n) : StkSep Mi st a n := by
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨h1, ?_, h3⟩
  simp only [BasicSqr.freeP, BasicSqr.freeN] at h2 ⊢
  have hlc := h.sok.2.2.2.2.2.1
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
  · rw [e1, e2, eW, eC]; rw [eL] at e3; unfold Apart at h2 ⊢; omega
  · have := apart_of_held (h.core.ext.held hh) hin hap
    unfold Apart at this ⊢; omega

/-- an operand range held in `L` and outside the window keeps its bytes from the entry to `Mi` -/
theorem LB.rd (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {a n : Nat}
    (hh : Held R L a n) (ho : Outside a n (win s W 88)) (hs : StkSep s.mem st a n) (hp : Apart a n p (8 * (xl + yl))) :
    Mi.readLE a n = s.mem.readLE a n := by
  rw [← h.core.rd hh ho]
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  obtain ⟨h1, h2, -⟩ := hs
  simp only [BasicSqr.freeP, BasicSqr.freeN] at h2
  simp only [win, outside_cons, outside_nil, and_true] at ho
  unfold Apart at h1 h2 hp
  refine Held.readLE2 (h.core.ext.held hh) h.fr h.lf ?_ ?_
  · simp only [winA, outside_cons, outside_nil, and_true]; omega
  · simp only [lws, stkWs, outside_cons, outside_nil, and_true]; rw [eW, eL, eC]; omega

end

end FvModexp.Arm64.NatMul
