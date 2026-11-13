import FvModexp.Proofs.Amd64.Nat.DivBigRel
import FvModexp.Proofs.Amd64.Nat.DivOneB

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u ≥ v` (`len v ≥ 2`): `divLarge`'s precondition at its entry (pure)

Port of `Arm64/Nat/DivBigP.lean` (`l_pre`) to amd64's `DivLarge.Pre` (`u = z2`, `uIn = u`, `vIn = v`; the stack args
at `RSP - 232 …` = `X.regs 4 + 8 …`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatDiv

/-- the threshold globals and the write-barrier flag survive a window-only frame
(adapted from fv-modexp top's arm64 `globals_win`, Proofs/Arm64/Nat/DivBigP.lean) -/
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

/-- `len v ≤ len u` when `v ≤ u` (both normalised, `v ≠ 0`) -/
theorem vl_le {m : Janus.Arm64.Memory} {u ul v vl : Nat} (hu : NatNorm m u ul) (hv : NatNorm m v vl) (hv0 : 0 < vl)
    (hge : natVal m v vl ≤ natVal m u ul) : vl ≤ ul := by
  rcases Nat.lt_or_ge (natVal m v vl) (natVal m u ul) with h1 | h1
  · exact len_le_of_lt hv h1
  · have : natVal m u ul = natVal m v vl := by omega
    rcases hv with h0 | ht
    · omega
    · refine Nat.le_of_not_lt fun hc => ?_
      have h2 := natVal_ge1 m v vl (by omega) ht
      have h3 := natVal_lt m u ul
      have h4 : 2 ^ (64 * ul) ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `DivLarge.Pre` at `divLarge`'s entry -/
theorem l_pre {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl)
    (X : State) (hX : AtL zp zl zc st z2 z2l z2c u ul uc v vl vc s X) :
    DivLarge.Pre R b L (DivLarge.cost dc (stLen X.mem st) ul vl) zp zc st z2 z2c u ul v vl X := by
  have hp := hpre.f
  have hce0 := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, hro, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hF := hX.mf
  have hspn := sp240 hX.sp (by omega)
  have hce : CallEnv R L X 41272 112 :=
    CallEnv.callee hce0 hspn hX.r14 hX.fs (by decide) (by decide) (by decide) hF hX.reg
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hp.sok
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have ew : stW X.mem st = stW s.mem st := hrd _ _ (by omega)
  have el : stLen X.mem st = stLen s.mem st := hrd _ _ (by omega)
  have ec : stCap X.mem st = stCap s.mem st := hrd _ _ (by omega)
  have hwin : ∀ a n, Outside a n (win s 41512 112) → Outside a n (win X 41272 112) := fun a n h =>
    winX hspn hb' h
  have hvl : vl ≤ ul := vl_le hp.un hp.vn (by omega) hge
  have wr : ∀ p c, EvenHyp.WrOut R L s 41512 112 p c → EvenHyp.WrOut R L X 41272 112 p c := by
    intro p c ⟨h1, h2, h3⟩
    refine ⟨h1, fun hc => ?_, fun hc => ⟨hwin _ _ (h3 hc).1, by rw [hX.r14, hX.fs]; exact (h3 hc).2⟩⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  have rd : ∀ p c, EvenHyp.RdIn R L s 41512 112 p c → EvenHyp.RdIn R L X 41272 112 p c := by
    intro p c ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, by rw [hacc]; exact h2, h3, h4, hwin _ _ h5⟩
  have hvw := hp.vo.2.2.2.2
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hz := hp.pw zp zc (by simp)
  have hz2 := hp.pw z2 z2c (by simp)
  unfold DivLarge.Pre
  rw [ew, el, ec, hspn, hX.fs, hX.r14]
  refine ⟨hce, hp.sv, globals_win hp.gl hF ?gw hwin, wr _ _ hp.zo, wr _ _ hp.z2o, rd _ _ hp.uo, rd _ _ hp.vo,
    hv2, hvl, hp.ul9, ?vn, hp.zz2, fun hc => ⟨(hz hc).1, (hz hc).2.1⟩, fun hc => (hz2 hc).2.1,
    Or.inr fun hc => (hz2 hc).1, ⟨?sok, ?sw, by rw [hX.r14]; exact hp.hdr.1, ?sarr⟩,
    hp.sl, fun hc => ⟨(hz hc).2.2.1, (hz hc).2.2.2⟩, fun hc => ⟨(hz2 hc).2.2.1, (hz2 hc).2.2.2⟩,
    ⟨hp.us, hp.uf⟩, ⟨hp.vs, hp.vf⟩, hp.hdr.2.1, hp.hdr.2.2, hp.w0, hp.st0, ⟨hp.zg, hp.z2g, hp.sg, hp.fg⟩, ?cost,
    ?inv, ?i0, ?i1, ?i3, ?i4, hp.tls.1, hp.tls.2⟩
  case gw =>
    have := hp.gl.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  case vn =>
    rcases hp.vn with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hrd _ _ (by omega)]; exact h)
  case sok =>
    refine ⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, ?_, by rw [el, ec]; exact hlc, by rw [ec]; exact hc40⟩
    rw [ew, ec]; intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  case sw => have := hwin _ _ hp.sw; simpa only [win, hspn] using this
  case sarr =>
    intro hc
    rw [ec] at hc; rw [ew, ec]
    have := hwin _ _ (hp.sa hc).1
    exact ⟨by simpa only [win, hspn] using this, by rw [hX.r14]; exact (hp.sa hc).2⟩
  case cost =>
    have := hp.cost; simp only [cost] at this; omega
  case inv => exact FvModexp.Amd64.NatAdd.inv_win hF hout hb' hp.inv
  case i0 => rw [show (s.regs 4).toNat - 240 + 8 = (s.regs 4).toNat - 232 by omega]; exact hX.i0
  case i1 => rw [show (s.regs 4).toNat - 240 + 16 = (s.regs 4).toNat - 224 by omega]; exact hX.i1
  case i3 => rw [show (s.regs 4).toNat - 240 + 32 = (s.regs 4).toNat - 208 by omega]; exact hX.i3
  case i4 => rw [show (s.regs 4).toNat - 240 + 40 = (s.regs 4).toNat - 200 by omega]; exact hX.i4

end FvModexp.Amd64.NatDiv
