import FvModexp.Proofs.Amd64.NatQ.MulLoopRel

/-!
# [amd64 port (divmc s45) of the Q-form Arm64/NatQ/MulLoopEnv.lean — TIGHT COSTS] `nat.mul` (amd64), chunk loop: the environment of an inner call from `LB`

`LB.dl` (read-only data), `LB.grd` (stack guard), `LB.callee` (`CallEnv` at `RSP - 264`), `LB.stk` / `LB.stkPre`
(`StkPre` at an inner call), `LB.glob` (threshold globals), `LB.sep` (an operand range kept `StkSep` at `Mi`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep tls)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

/-- the frame from the entry to `Mi` (the result range dropped when it is fresh, i.e. inside `R.rt`) -/
theorem LB0.frE (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    MemFrame s.mem Mi (R.rt ++ win s W 88 ++ lws s.mem st p (xl + yl)) := by
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have e : lws M st p (xl + yl) = lws s.mem st p (xl + yl) := by simp only [lws, stkWs]; rw [eW, eL, eC]
  rw [← e]
  exact h.core.F.trans h.fr fun a n ho => ⟨by simp only [outside_append] at ho ⊢; exact ⟨ho.1.1, ho.1.2⟩, ho⟩

/-- the read-only data stays loaded -/
theorem LB0.dl (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    Extracted.program.DataLoaded Mi := by
  obtain ⟨⟨-, ⟨hb, ha', hw⟩, hal, hdl, -, -, -, -, hro, -⟩, -⟩ := h.core.pre
  simp only [regSP] at hb ha' hw
  have hzlive : NatLive s.mem R L zp zc := h.core.pre.2.2.2.2.2.1.2.2.1.2.1
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, -, hsacc, -, hnl, hlc, -⟩, -⟩ := hsp
  have hcap := h.core.cap
  rcases h.core.kind with ⟨hpz, hcz⟩ | ⟨hin, -, -⟩
  · rw [← hpz, ← hcz] at hzlive
    have hfr : MemFrame s.mem Mi (R.rt ++ (win s W 88 ++ lws s.mem st p (xl + yl))) := by
      rw [← List.append_assoc]; exact h.frE
    refine dataLoaded_frame64 hdl h.reg hro hfr fun r hr hlt => ?_
    simp only [win, lws, stkWs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · obtain ⟨-, -, hacc, -⟩ := hzlive (by simp only at hlt; omega)
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)
    · exact Janus.Arm64.Memory.accessible_mono _ hsacc (by simp only; omega) (by simp only; omega)
    · simp only at hlt
      obtain ⟨-, -, hacc, -⟩ := hnl (by omega)
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)
  · have hfr : MemFrame s.mem Mi (R.rt ++ (win s W 88 ++ stkWs s.mem st)) := by
      refine h.frE.mono fun a n ho => ?_
      simp only [lws, outside_append, outside_cons] at ho ⊢
      exact ⟨⟨ho.1, ho.2.1⟩, NatSub.outside_of_inRanges ho.1 (hin.sub (Nat.le_refl _) (by omega)), ho.2.2⟩
    refine dataLoaded_frame64 hdl h.reg hro hfr fun r hr hlt => ?_
    simp only [win, stkWs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · exact Janus.Arm64.Memory.accessible_mono _ hsacc (by simp only; omega) (by simp only; omega)
    · simp only at hlt
      obtain ⟨-, -, hacc, -⟩ := hnl (by omega)
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)

/-- the stack-NatSqr.guard word keeps its value -/
theorem LB0.grd (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    Mi.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
  obtain ⟨hW, hWs, -, -, hout, hgr, hga, hcap, -⟩ := h.lay
  have h40 := h.h40
  have hpg := h.core.pg (by omega)
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, -, -, hstg, -, hfg, -⟩ := hsp
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hstg hfg
  unfold Apart at hpg hstg hfg hga
  refine h.frE.readLE _ _ ?_
  simp only [win, lws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨hgr, by omega⟩, by omega, by omega, by omega⟩

/-- the TLS slot (`FS - 8`, the goroutine pointer) keeps its value -/
theorem LB0.tlsv (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    Mi.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, ⟨-, htrt, htw⟩⟩, -⟩ := h.core.pre
  have hpt := h.core.ptls (by have := h.h40; have := h.core.cap; omega)
  have hcap := h.core.cap
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hstt, -, hft⟩ := hsp
  simp only [tls, BasicSqr.freeP, BasicSqr.freeN] at hpt hstt hft
  unfold Apart at hpt hstt hft htw
  refine h.frE.readLE _ _ ?_
  simp only [win, lws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨htrt, by omega⟩, by omega, by omega, by omega⟩

/-- the call environment of a callee at `RSP - 264` (window inside ours, `above ≤ 88`) -/
theorem LB0.callee (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {S1 : State}
    {stk1 above1 : Nat} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = Mi)
    (hfs : S1.fsBase = s.fsBase) (hk : 264 + stk1 ≤ W) (ha : above1 ≤ 88) : CallEnv R Lk S1 stk1 above1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩, -⟩ :=
    h.core.pre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgrd := h.grd
  have htv := h.tlsv
  have hLs1 := h.wsep
  obtain ⟨ns, hLk, hn, -⟩ := h.ext
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hm, h.frE.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg, hm, hgrd, hsp]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hm, h.frE.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · rw [hm]; exact h.dl
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]
    rw [hLk] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs1 r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := NatSub.outside_of_inRanges hout (hn r hr).1; omega
  · rw [hfs]; exact htb
  · rw [hfs, hm, h.frE.accessible]; exact htr
  · rw [hfs, hm, htv, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

/-- the stack's current array and free part: outside the window, apart from the NatSqr.guard word and the header, held -/
theorem LB.stk (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
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
      have := NatSub.outside_of_inRanges (hout.of_sub (a := (s.regs 4).toNat - W) (n := W + 88) (by omega) (by omega)) hin
      simp only [win, outside_cons, outside_nil, and_true]; omega
    refine ⟨fun _ => ⟨hw _ _ (by omega) (by omega), by unfold Apart; omega⟩, by unfold Apart; omega,
      hw _ _ (by omega) (by omega), by unfold Apart at hst ⊢; omega, hh.sub (by omega) (by omega), ?_⟩
    have := NatSub.outside_of_inRanges hgrt hin
    unfold Apart; omega

/-- the stack's current array and free part are apart from the TLS slot (amd64) -/
theorem LB.stkT (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    (0 < stCap Mi st → Apart (stW Mi st) (8 * stCap Mi st) (tls s) 8) ∧
    Apart (BasicSqr.freeP Mi st) (BasicSqr.freeN Mi st) (tls s) 8 := by
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, ⟨-, htrt, -⟩⟩, -⟩ := h.core.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsatl, hftl⟩ := hsp
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have hlc := h.sok.2.2.2.2.2.1
  simp only [tls, BasicSqr.freeP, BasicSqr.freeN] at hsatl hftl hlc ⊢
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, -⟩
  · simp only [e1, e2, eW, eC] at hlc ⊢; rw [eL] at e3
    refine ⟨hsatl, ?_⟩
    have := hftl; unfold Apart at this ⊢; omega
  · have hto := NatSub.outside_of_inRanges htrt hin
    exact ⟨fun _ => by unfold Apart; omega, by unfold Apart; omega⟩

/-- **`StkPre` at an inner call** (`RSP - 264`, window `W' + 264 ≤ W`, above `≤ 88`) -/
theorem LB.stkPre (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {S1 : State} {W' a : Nat}
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = Mi)
    (hfs : S1.fsBase = s.fsBase) (hk : 264 + W' ≤ W) (ha : a ≤ 88) : StkPre R Lk S1 W' a st := by
  obtain ⟨hW, hWs, -⟩ := h.lay
  have hsp' : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨hst0, -, hstw, hstg, -, -, -, -, hstwb, -, hsgA, -, hsttl, -, -⟩ := hsp'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.stk
  obtain ⟨t1, t2⟩ := h.stkT
  have hwin : ∀ x k, Outside x k (win s W 88) → Outside x k (win S1 W' a) := by
    intro x k hx; simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hsp]; omega
  subst hm
  simp only [StkPre, NatSqr.guard, tls, hg, hfs] at h1 h2 hstg hsttl t1 t2 ⊢
  exact ⟨hst0, h.sok, hwin _ _ hstw, hstg, fun hc => ⟨hwin _ _ (h1 hc).1, (h1 hc).2⟩, h2, hwin _ _ h3, h4, hstwb, h5,
    hsgA, h6, hsttl, t1, t2⟩

/-- the threshold globals at `Mi` -/
theorem LB0.glob (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {w' : List (Nat × Nat)}
    (hw : ∀ x k, Outside x k (win s W 88) → Outside x k w') : RunIface.Globals R Mi w' := by
  have hgl : RunIface.Globals R s.mem (win s W 88) := h.core.pre.2.2.2.1
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  have hpg := h.core.pgA (by have := h.core.cap; have := h.h40; omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsgA, hfgA⟩ := hsp
  have hgw : Outside RunIface.gA 32 (win s W 88) := hgl.2.2.2.2.2.2.2.2.2.1
  have hcap := h.core.cap
  have hfr : MemFrame s.mem Mi (R.rt ++ (win s W 88 ++ lws s.mem st p (xl + yl))) := by
    rw [← List.append_assoc]; exact h.frE
  refine NatSqr.globals_frame hgl hfr ?_ hw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfgA
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  unfold Apart at hpg hsgA hfgA
  simp only [win, lws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  omega

/-- an operand range held in `L`, outside the window and `StkSep` at the entry stays readable and `StkSep` at `Mi` -/
theorem LB.sep (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {a n : Nat}
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
theorem LB0.rd (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {a n : Nat}
    (hh : Held R L a n) (ho : Outside a n (win s W 88)) (hs : StkSep s.mem st a n) (hp : Apart a n p (8 * (xl + yl))) :
    Mi.readLE a n = s.mem.readLE a n := by
  rw [← h.core.rd hh ho]
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  obtain ⟨h1, h2, -⟩ := hs
  simp only [BasicSqr.freeP, BasicSqr.freeN] at h2
  simp only [win, outside_cons, outside_nil, and_true] at ho
  unfold Apart at h1 h2 hp
  refine Held.readLE2 (h.core.ext.held hh) h.fr h.lf ?_ ?_
  · simp only [win, outside_cons, outside_nil, and_true]; omega
  · simp only [lws, stkWs, outside_cons, outside_nil, and_true]; rw [eW, eL, eC]; omega

end

end FvModexp.Amd64.Q.NatMul
