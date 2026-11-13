import FvModexp.Proofs.Amd64.NatQ.RemDivC
import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): `div`'s precondition at `CALL nat.div` (pure; twin of Arm64/NatQ/RemDvPre.lean, divmc s59)

`q = (tq, k, k)` with `tq = stW M + 8·len` (the scratch from `stk.nat(k)`), `z2 := z`, `u`, `v` (stack arguments at
`RSP+8 … RSP+48` of the callee entry `X`), stack `st` (now of length `len + rnd k`), live set `L1`, budget `b1` (`SN`).
`SN.frameX` moves `SN` across the stack-argument stores and the push (`AtDiv.mf`, inside `rem`'s window).
The region `F = [tq, stW M + 8·cap M)` is the old free part (stack kept) or inside the fresh array (in `R.rt`, apart
from `L`): `SN.regH` / `SN.regO` give its apartness from every held range apart from the old free part, and from the
window / guard word / `gA` / the TLS slot.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

open FvModexp.Amd64.NHyp (RemPreQ freeOf)

variable {H : Nat}

theorem rnd_ge (k : Nat) : k ≤ StackNat.rnd k ∧ StackNat.rnd k ≤ k + 3 := by
  simp only [StackNat.rnd]; omega

theorem kq_pos (ul vl : Nat) : 0 < kq ul vl := by simp only [kq]; omega

theorem kq_le (ul vl : Nat) : kq ul vl ≤ ul + 1 := by simp only [kq]; omega

set_option maxRecDepth 20000 in
/-- `SN` across a frame inside `rem`'s window (the stack-argument stores and the push before `CALL nat.div`) -/
theorem SN.frameX {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st k : Nat} {s : State} {M M' : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hN : SN R b H L st k s M L1 b1) {w1 w2 : Nat}
    (hF : MemFrame M M' [(w1, w2)]) (hreg : M'.regions = M.regions)
    (hw : (s.regs 4).toNat - 41720 ≤ w1 ∧ w2 ≤ (s.regs 4).toNat + 112)
    (hst : Outside st 24 (win s 41720 112)) (hrt : Outside w1 (w2 - w1) R.rt)
    (hLs : LiveSep L (win s 41720 112)) (hLs1 : LiveSep L1 (win s 41720 112)) :
    SN R b H L st k s M' L1 b1 := by
  simp only [win, outside_cons, outside_nil, and_true] at hst
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41720 ∨ (s.regs 4).toNat + 112 ≤ a) →
      M'.readLE a n = M.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n v, M'.accessible a n v = M.accessible a n v := fun a n v => hF.accessible a n v
  have eW : stW M' st = stW M st := hrd _ _ (by omega)
  have eL : stLen M' st = stLen M st := hrd _ _ (by omega)
  have eC : stCap M' st = stCap M st := hrd _ _ (by omega)
  refine ⟨hN.ext, by rw [stkR_congr eC]; exact hN.bud, ?inv, ?sok, by rw [eL]; exact hN.len,
    fun h => by rw [eW, eC]; exact hN.kept h, fun h => by rw [eW, eC]; exact hN.fresh h,
    fun h => by rw [eW, eC]; exact hN.arrL h, ?mf, ?lf, by rw [hreg]; exact hN.reg⟩
  case inv =>
    refine RtInv.inv_frame' hF (fun r hr => ?_) hN.inv
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hrt
  case sok =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hN.sok
    refine ⟨a1, a2, by rw [hacc]; exact a3, a4, ?_, by rw [eL, eC]; exact a6, by rw [eC]; exact a7⟩
    show NatLive M' R L1 (stW M' st) (stCap M' st)
    rw [eW, eC]; intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hacc]; exact b3, b4⟩
  case mf =>
    refine hN.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [List.append_assoc, outside_append, win, outside_cons, outside_nil, and_true] at ho
    simp only [outside_cons, outside_nil, and_true]; omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [← hN.lf.readLE a n hin ho]
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    exact hF.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)

/-- a held range apart from the old free part is apart from the region `F` -/
theorem SN.regH {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st k : Nat} {s : State} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hN : SN R b H L st k s M L1 b1) {a n : Nat} (hH : Held R L a n)
    (hA : Apart a n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) :
    Apart a n (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) := by
  have hlc := hN.sok.2.2.2.2.2.1
  have hl := hN.len
  by_cases hg : stLen s.mem st + StackNat.rnd k ≤ stCap s.mem st
  · rw [(hN.kept hg).1, (hN.kept hg).2]; exact hA
  · obtain ⟨hin, hap⟩ := hN.fresh (by omega)
    have h2 : Apart a n (stW M st) (8 * stCap M st) := by
      rcases hH with h | h
      · obtain ⟨r, hr, h1, h2⟩ := h
        have := hap r hr; unfold Apart at this ⊢; omega
      · exact InRanges.apart hin h
    unfold Apart at h2 ⊢; omega

set_option maxRecDepth 20000 in
/-- the region `F` is outside the window and apart from the guard word, `gA` and the TLS slot; with the stack
array (when `0 < cap`) apart from the TLS slot -/
theorem SN.regO {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {zp zl zc st up ul uc vp vl vc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : RemPreQ R b H L 41720 112 zp zl zc st up ul uc vp vl vc (need ul vl) c s)
    (hN : SN R b H L st (kq ul vl) s M L1 b1) :
    Outside (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) (win s 41720 112) ∧
      Apart (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) ((s.regs 14).toNat + 16) 8 ∧
      Apart (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) RunIface.gA 32 ∧
      Apart (stW M st + 8 * stLen s.mem st) (8 * (stCap M st - stLen s.mem st)) (s.fsBase.toNat - 8) 8 ∧
      (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (s.fsBase.toNat - 8) 8) := by
  obtain ⟨-, hce, -, hgl, -, -, -, -, -, -, -, -, harr, -, -, -, -, -, ⟨-, hfT⟩, -, -, hfgA, -, -, hta, -⟩ := hpre
  obtain ⟨-, -, -, -, hout, -, hgr, -, -, -, htrt, -⟩ := hce
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, -, -, -, -⟩ := hgl
  have hlc := hN.sok.2.2.2.2.2.1
  have hl := hN.len
  have hr := rnd_ge (kq ul vl)
  have hk := kq_pos ul vl
  by_cases hg : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap s.mem st
  · rw [(hN.kept hg).1, (hN.kept hg).2]
    obtain ⟨h1, h2⟩ := harr (by omega)
    simp only [win, outside_cons, outside_nil, and_true] at h1 ⊢
    exact ⟨by omega, by unfold Apart at h2 ⊢; omega, hfgA, hfT, hta⟩
  · obtain ⟨hin, -⟩ := hN.fresh (by omega)
    have a1 := InRanges.apart hin hout
    have a2 := InRanges.apart hin hgr
    have a3 := InRanges.apart hin hgArt
    have a4 := InRanges.apart hin htrt
    unfold Apart at a1 a2 a3 a4
    refine ⟨?_, ?_, ?_, ?_, fun _ => by unfold Apart; omega⟩
    · simp only [win, outside_cons, outside_nil, and_true]; omega
    all_goals (unfold Apart; omega)

/-- the scratch `q` and the new free part lie in the region `F` (`len' = len + rnd k ≤ cap'`), `q` before the free part -/
theorem sub_F {ln lM C k W a n : Nat} (hl : lM = ln + StackNat.rnd k) (hlc : lM ≤ C)
    (h : Apart a n (W + 8 * ln) (8 * (C - ln))) :
    Apart a n (W + 8 * ln) (8 * k) ∧ Apart a n (W + 8 * lM) (8 * (C - lM)) := by
  have := rnd_ge k
  unfold Apart at h ⊢; omega

theorem sub_F' {ln lM C k W a n : Nat} (hl : lM = ln + StackNat.rnd k) (hlc : lM ≤ C)
    (h : Apart (W + 8 * ln) (8 * (C - ln)) a n) :
    Apart (W + 8 * ln) (8 * k) a n ∧ Apart (W + 8 * lM) (8 * (C - lM)) a n := by
  have := rnd_ge k
  unfold Apart at h ⊢; omega

theorem q_free {ln lM C k W : Nat} (hl : lM = ln + StackNat.rnd k) :
    Apart (W + 8 * ln) (8 * k) (W + 8 * lM) (8 * (C - lM)) := by
  have := rnd_ge k
  unfold Apart; omega

theorem len_ok {ln ul k : Nat} (hneed : ln + need ul 0 ≤ 2 ^ 16) (hk1 : k ≤ ul + 1) :
    ln + StackNat.rnd k + 16 * ul + 64 ≤ 2 ^ 16 := by
  have := rnd_ge k; simp only [need] at hneed; omega

theorem lenH_ok {ln ul k H : Nat} (hneed : ln + need ul 0 ≤ H) (hk1 : k ≤ ul + 1) :
    ln + StackNat.rnd k + 16 * ul + 64 ≤ H := by
  have := rnd_ge k; simp only [need] at hneed; omega

theorem cost_ok {b b1 c R0 R1 : Nat} (hc : c + R0 ≤ b) (hb : b - R0 + R1 ≤ b1) : c + R1 ≤ b1 := by omega

/-- the threshold globals and the write-barrier flag survive a frame they are outside of (copy of top's
`globals_win`, Amd64/NatQ/DivBigP.lean, so that rem does not import the division chain) -/
theorem globals_win {R : RtInv} {m m' : Janus.Arm64.Memory} {w w' ws : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' ws) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (hg.of_sub (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

/-- a range apart from the header and the old free part is outside `stkWs` -/
theorem out_stkWs {m : Memory} {st a n : Nat} (hlc : stLen m st ≤ stCap m st) (h1 : Apart a n st 24)
    (h2 : Apart a n (stW m st + 8 * stLen m st) (8 * (stCap m st - stLen m st))) : Outside a n (stkWs m st) := by
  simp only [stkWs, outside_cons, outside_nil, and_true]; unfold Apart at h1 h2; omega

set_option maxRecDepth 20000 in
/-- the call environment one frame down, across a frame `R.rt ++ window ++ ws` (`callEnv_shift`, Amd64/NatQ/MulOps.lean,
with the extra written ranges `ws`) -/
theorem callEnv_shiftW {R : RtInv} {L L1 ws : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab))
    (hF1 : MemFrame s.mem S1.mem (R.rt ++ (win s W ab ++ ws)))
    (hgws : Outside ((s.regs 14).toNat + 16) 8 ws) (htws : Outside (s.fsBase.toNat - 8) 8 ws)
    (hws : ∀ r ∈ ws, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 ≤ f + ab) (hf8 : f % 8 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgr' : S1.mem.readLE ((S1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, hgws⟩)
  have htls : S1.mem.readLE (S1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨htrt, by omega, htws⟩)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF1.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF1.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro hF1 (by
      intro r hr hlt
      rcases List.mem_append.1 hr with hr | hr
      · simp only [win, List.mem_singleton] at hr; subst hr
        simp only; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
      · exact hws r hr hlt)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`div`'s precondition** at the callee entry `X` (`RSP = entry RSP - 208`, the stack arguments `u`, `v` at
`RSP+8 … RSP+48`, memory after `stk.nat` + the stores: `SN … X.mem`) -/
theorem dv_pre {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl vc : Nat} {s X : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hpre : RemPreQ R b H L 41720 112 zp zl zc st up ul uc vp vl vc (need ul vl) (cd ul vl + stkR H s.mem st) s)
    (hN : SN R b H L st (kq ul vl) s X.mem L1 b1)
    (hsp : X.regs 4 = s.regs 4 - 208#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (a1 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = up) (a2 : X.mem.readLE ((s.regs 4).toNat - 192) 8 = ul)
    (a3 : X.mem.readLE ((s.regs 4).toNat - 184) 8 = uc) (a4 : X.mem.readLE ((s.regs 4).toNat - 176) 8 = vp)
    (a5 : X.mem.readLE ((s.regs 4).toNat - 168) 8 = vl) (a6 : X.mem.readLE ((s.regs 4).toNat - 160) 8 = vc) :
    ExpHyp.DivPreQ R b1 H (cd ul vl + stkR H X.mem st) L1 41512 112 (stW X.mem st + 8 * stLen s.mem st) (kq ul vl)
      (kq ul vl) st zp zl zc up ul uc vp vl vc X := by
  have hO := hN.regO hpre
  have hce0 := hpre.2.1
  obtain ⟨-, hce, hsv, hgl, -, -, hzlc, hzo, hins, hsok0, hsw, hsg, harr, hc0, hneed, -, hwbs, hfree, ⟨hstT, hfT⟩,
    hzst, hsgA, hfgA, hcst, hadx, -, -, hvl0, -, hst0, hlv⟩ := hpre
  obtain ⟨-, ⟨hb', -, hw⟩, -, -, hout, hga, hgr, hLs, -, -, htrt, -⟩ := hce
  simp only [regSP] at hb' hw
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 208 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := hN.mf.accessible
  have hwinX : ∀ a n, Outside a n (win s 41720 112) → Outside a n (win X 41512 112) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hspn]; omega
  obtain ⟨-, hsth, hstacc, -, hnl0, hlc0, -⟩ := hsok0
  have hMF : MemFrame s.mem X.mem (R.rt ++ (win s 41720 112 ++ stkWs s.mem st)) := by
    simpa only [List.append_assoc] using hN.mf
  have hLF : LiveFrame s.mem X.mem L (win s 41720 112 ++ stkWs s.mem st) :=
    ⟨fun a n hin ho => hN.lf.readLE a n hin (by rw [outside_append] at ho; exact ho.2)⟩
  have hrdH : ∀ a n, Held R L a n → Outside a n (win s 41720 112) → Outside a n (stkWs s.mem st) →
      X.mem.readLE a n = s.mem.readLE a n := fun a n hh h1 h2 => hh.readLE hMF hLF (by
    rw [outside_append]; exact ⟨h1, h2⟩)
  obtain ⟨⟨hu40, huacc, hu48, huh, huw⟩, hu9, hun, hust, hufr, hzu⟩ := hins up ul (by simp)
  obtain ⟨⟨hv40, hvacc, hv48, hvh, hvw⟩, hv9, hvn, hvst, hvfr, hzv⟩ := hins vp vl (by simp)
  clear hins
  have hsok := hN.sok
  obtain ⟨-, -, -, -, hnl, hlc, -⟩ := hsok
  have hl := hN.len
  have hr := rnd_ge (kq ul vl)
  have hk := kq_pos ul vl
  have hk1 := kq_le ul vl
  have hC : 0 < stCap X.mem st := by omega
  have hlc' : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap X.mem st := hl ▸ hlc
  obtain ⟨hw8, hwh, hwacc, hw48⟩ := hnl hC
  have hgws : Outside ((s.regs 14).toNat + 16) 8 (stkWs s.mem st) := by
    refine out_stkWs hlc0 hsg.symm ?_
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with hc | hc
    · rw [hc0 hc, hc]; unfold Apart; omega
    · have := (harr hc).2; unfold Apart at this ⊢; omega
  have hLs1 : LiveSep L1 (win s 41720 112) := hN.ext.liveSep hLs (fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega))
  have e8 : ∀ j, (X.regs 4).toNat + j = (s.regs 4).toNat - 208 + j := fun j => by rw [hspn]
  unfold ExpHyp.DivPreQ
  rw [hl]
  refine ⟨by rw [e8, show (s.regs 4).toNat - 208 + 8 = (s.regs 4).toNat - 200 by omega]; exact a1,
    by rw [e8, show (s.regs 4).toNat - 208 + 16 = (s.regs 4).toNat - 192 by omega]; exact a2,
    by rw [e8, show (s.regs 4).toNat - 208 + 24 = (s.regs 4).toNat - 184 by omega]; exact a3,
    by rw [e8, show (s.regs 4).toNat - 208 + 32 = (s.regs 4).toNat - 176 by omega]; exact a4,
    by rw [e8, show (s.regs 4).toNat - 208 + 40 = (s.regs 4).toNat - 168 by omega]; exact a5,
    by rw [e8, show (s.regs 4).toNat - 208 + 48 = (s.regs 4).toNat - 160 by omega]; exact a6,
    ?ce, hsv, ?gl, Nat.le_refl _, hzlc, ?qo, ?zo, ?ui, ?vi, hu9, hvl0, hv9, ?un, ?vn, hN.sok, hwinX _ _ hsw, ?sarr,
    ?len, fun h => absurd h (Nat.pos_iff_ne_zero.mp hC), hust, ?uF, hvst, ?vF, by omega,
    ⟨by rw [h14]; exact hsg, hwbs, ?stF⟩, ⟨by rw [hfs]; exact hstT, ?fT⟩, ?qg, fun hc => (hzst hc).2.2,
    hsgA, ?fgA, ?qz, ?pw, ?cost, by rw [hacc]; exact hadx, fun _ => by rw [hfs]; exact hO.2.2.2.2 hC,
    by rw [h14]; exact hN.inv⟩
  case ce =>
    refine callEnv_shiftW hce0 hLs1 hMF hgws (out_stkWs hlc0 hstT.symm hfT.symm) ?_ hspn h14 hfs hN.reg
      (by omega) (by omega) (by omega)
    intro r hr hlt
    simp only [stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hstacc
    · simp only at hlt ⊢
      obtain ⟨-, -, harr0, -⟩ := hnl0 (by omega)
      exact Janus.Arm64.Memory.accessible_mono _ harr0 (by omega) (by omega)
  case gl =>
    refine globals_win hgl hN.mf ?_ hwinX
    obtain ⟨-, -, -, -, -, -, -, -, hgArt, hgAw, -, -, -⟩ := hgl
    rw [outside_append, outside_append]
    exact ⟨⟨hgArt, hgAw⟩, out_stkWs hlc0 hsgA.symm hfgA.symm⟩
  case qo =>
    refine ⟨by omega, fun _ => ⟨by omega, hwh.sub (by omega) (by omega),
      Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega), by omega⟩, fun _ => ⟨?_, ?_, ?_⟩⟩
    · exact hwinX _ _ (hO.1.of_sub (by omega) (by omega))
    · rw [h14]; exact (sub_F' rfl hlc' hO.2.1).1
    · rw [hfs]; exact (sub_F' rfl hlc' hO.2.2.2.1).1
  case zo =>
    obtain ⟨h1, h2, h3⟩ := hzo
    refine ⟨h1, fun hc => ?_, fun hc => ⟨hwinX _ _ (h3 hc).1, by rw [h14]; exact (h3 hc).2.1,
      by rw [hfs]; exact (h3 hc).2.2⟩⟩
    obtain ⟨b1, b2, b3, b4⟩ := h2 hc; exact ⟨b1, hN.ext.held b2, by rw [hacc]; exact b3, b4⟩
  case ui => exact ⟨hu40, by rw [hacc]; exact huacc, hu48, hN.ext.held huh, hwinX _ _ huw⟩
  case vi => exact ⟨hv40, by rw [hacc]; exact hvacc, hv48, hN.ext.held hvh, hwinX _ _ hvw⟩
  case un =>
    rcases hun with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos ul with h0 | h0
      · exact Or.inl h0
      refine Or.inr ?_
      have ho := out_stkWs hlc0 hust hufr
      rw [hrdH _ _ (huh.sub (by omega) (by omega)) (huw.of_sub (by omega) (by omega))
        (ho.of_sub (by omega) (by omega))]; exact h
  case vn =>
    rcases hvn with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos vl with h0 | h0
      · exact Or.inl h0
      refine Or.inr ?_
      have ho := out_stkWs hlc0 hvst hvfr
      rw [hrdH _ _ (hvh.sub (by omega) (by omega)) (hvw.of_sub (by omega) (by omega))
        (ho.of_sub (by omega) (by omega))]; exact h
  case sarr =>
    intro _
    refine ⟨?_, ?_⟩
    · have := hO.1
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢
      rw [hspn]
      by_cases hg : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap s.mem st
      · rw [(hN.kept hg).1, (hN.kept hg).2]
        have := (harr (by omega)).1
        simp only [win, outside_cons, outside_nil, and_true] at this; omega
      · obtain ⟨hin, -⟩ := hN.fresh (by omega)
        have := InRanges.apart hin hout; unfold Apart at this; omega
    · rw [h14]
      by_cases hg : stLen s.mem st + StackNat.rnd (kq ul vl) ≤ stCap s.mem st
      · rw [(hN.kept hg).1, (hN.kept hg).2]; exact (harr (by omega)).2
      · obtain ⟨hin, -⟩ := hN.fresh (by omega)
        exact (InRanges.apart hin hgr).symm
  case len => exact len_ok (by simp only [need] at hneed ⊢; omega) hk1
  case uF => exact (sub_F rfl hlc' (hN.regH huh hufr)).2
  case vF => exact (sub_F rfl hlc' (hN.regH hvh hvfr)).2
  case stF => exact (sub_F rfl hlc' (hN.regH hsth hfree)).2
  case fT => rw [hfs]; exact (sub_F' rfl hlc' hO.2.2.2.1).2
  case qg => exact fun _ => (sub_F' rfl hlc' hO.2.2.1).1
  case fgA => exact (sub_F' rfl hlc' hO.2.2.1).2
  case qz =>
    intro _ hc
    exact (sub_F rfl hlc' (hN.regH ((hzo.2.1 hc).2.1) (hzst hc).2.1)).1.symm
  case pw =>
    intro p c hpc hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpc
    rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(sub_F rfl hlc' (hN.regH huh hufr)).1.symm, (sub_F rfl hlc' (hN.regH hvh hvfr)).1.symm,
        (sub_F rfl hlc' (hN.regH hsth hfree)).1.symm, q_free rfl⟩
    · exact ⟨hzu hc, hzv hc, (hzst hc).1, (sub_F rfl hlc' (hN.regH ((hzo.2.1 hc).2.1) (hzst hc).2.1)).2⟩
  case cost =>
    refine ⟨lenH_ok (by simp only [need] at hlv ⊢; omega) hk1, ?_⟩
    exact cost_ok hcst hN.bud

end FvModexp.Amd64.Q.NatRem
