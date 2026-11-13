import FvModexp.Proofs.Arm64.NatQ.DivRel
import FvModexp.Proofs.Arm64.Nat.DivmcCall

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivBigP.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64), `u ≥ v` (`len v ≥ 2`): `divLarge`'s precondition at its entry (pure)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

/-- the threshold globals and the write-barrier flag survive a window-only frame -/
theorem globals_win {R : RtInv} {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : RunIface.Globals R m w)
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `DivLarge.Pre` at `divLarge`'s entry (`SP' = SP - 240`, memory changed only in the window) -/
theorem l_pre {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul v vl : Nat} {s : State}
    (hpre : Pre R b H dc L zp zl zc st z2 z2l z2c u ul v vl s) (hsep : HdrSep s st)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl)
    (X : State) (hsp : X.sp = s.sp - 240#64) (h28 : X.regs 28 = s.regs 28)
    (hF : MemFrame s.mem X.mem (winA s 41504 112)) (hreg : X.mem.regions = s.mem.regions) :
    DivLarge.Pre R b H L (DivLarge.costQ dc ul vl) zp zc st z2 z2c u ul v vl X := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hp.ce
  have hspn : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hFw : MemFrame s.mem X.mem (win s 41504 112) := hF.mono fun a n h => by
    simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hFw.readLE a n (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hp.sok
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have ew : stW X.mem st = stW s.mem st := hrd _ _ (by omega)
  have el : stLen X.mem st = stLen s.mem st := hrd _ _ (by omega)
  have ec : stCap X.mem st = stCap s.mem st := hrd _ _ (by omega)
  obtain ⟨x1, x2, x3, x4, -⟩ := spX hsp (by omega)
  have hwin : ∀ a n, Outside a n (win s 41504 112) → Outside a n (win X 41264 112) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true, x1, x4] at h ⊢; omega
  have hvl : vl ≤ ul := by
    rcases Nat.lt_or_ge (natVal s.mem v vl) (natVal s.mem u ul) with h1 | h1
    · exact len_le_of_lt hp.vn h1
    · have : natVal s.mem u ul = natVal s.mem v vl := by omega
      rcases hp.vn with h0 | ht
      · omega
      · refine Nat.le_of_not_lt fun hc => ?_
        have h2 := natVal_ge1 s.mem v vl (by omega) ht
        have h3 := natVal_lt s.mem u ul
        have h4 : 2 ^ (64 * ul) ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
  have wr : ∀ p c, ExpHyp.WrOut R L s 41504 112 p c → ExpHyp.WrOut R L X 41264 112 p c := by
    intro p c ⟨h1, h2, h3⟩
    refine ⟨h1, fun hc => ?_, fun hc => ⟨hwin _ _ (h3 hc).1, by rw [h28]; exact (h3 hc).2⟩⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  have rd : ∀ p c, ExpHyp.RdIn R L s 41504 112 p c → ExpHyp.RdIn R L X 41264 112 p c := by
    intro p c ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, by rw [hacc]; exact h2, h3, h4, hwin _ _ h5⟩
  have hvw := hp.vo.2.2.2.2
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hz := hp.pw zp zc (by simp)
  have hz2 := hp.pw z2 z2c (by simp)
  unfold DivLarge.Pre
  rw [ew, el, ec]
  refine ⟨CallEnv.callee hp.ce hspn h28 (by decide) (by decide) (by decide) hFw hreg, hp.sv,
    globals_win hp.gl hFw ?gw (fun a n h => hwin a n h), wr _ _ hp.zo, wr _ _ hp.z2o, rd _ _ hp.uo, rd _ _ hp.vo,
    hv2, hvl, hp.ul9, ?vn, hp.zz2, fun hc => ⟨(hz hc).1, (hz hc).2.1⟩, fun hc => (hz2 hc).2.1,
    Or.inr fun hc => (hz2 hc).1, ⟨?sok, hwin _ _ hp.sw, by rw [h28]; exact hsep.1, ?sarr⟩,
    hp.sl, fun hc => ⟨(hz hc).2.2.1, (hz hc).2.2.2⟩, fun hc => ⟨(hz2 hc).2.2.1, (hz2 hc).2.2.2⟩,
    ⟨hp.us, hp.uf⟩, ⟨hp.vs, hp.vf⟩, hsep.2.1, hsep.2.2, ⟨hp.w0, hp.st0⟩, ⟨hp.zg, hp.z2g, hp.sg, hp.fg⟩, ?cost, ?inv⟩
  case gw =>
    have := hp.gl.2.2.2.2.2.2.2.2.2.1
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega
  case vn =>
    rcases hp.vn with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hrd _ _ (by omega)]; exact h)
  case sok =>
    refine ⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, ?_, by rw [el, ec]; exact hlc, by rw [ec]; exact hc40⟩
    rw [ew, ec]; intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  case sarr =>
    intro hc
    rw [ec] at hc; rw [ew, ec]
    exact ⟨hwin _ _ (hp.sa hc).1, by rw [h28]; exact (hp.sa hc).2⟩
  case cost =>
    have h1 := hp.cost
    refine ⟨by first | (rw [el]; omega) | omega, ?_⟩
    rw [stkR_congr ec]; simp only [costQ, DivLarge.costQ] at h1 ⊢; omega
  case inv =>
    rw [h28]; exact inv_frame_winA hF hout hb' (by omega) hp.inv

end FvModexp.Arm64.Q.NatDiv
