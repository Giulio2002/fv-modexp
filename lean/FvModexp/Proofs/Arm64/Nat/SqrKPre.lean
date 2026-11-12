import FvModexp.Proofs.Arm64.Nat.SqrCall

/-!
# `nat.sqr` (arm64): `KPre` at the call of `karatsubaSqr(stk, z[0:2n], x)` (`80 ≤ n`), one frame down (`W - 176`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

open FvModexp.Arm64.RunIface (Globals)

/-- the threshold globals and the write-barrier flag survive a frame that keeps them -/
theorem globals_frame {R : RtInv} {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : Globals R m w)
    (hF : MemFrame m m' (R.rt ++ ws)) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt.of_sub (by omega) (by omega), hg.of_sub (by omega) (by omega)⟩)
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ks_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hpx : Apart p (8 * c) xp (8 * xl))
    (hna : p + 8 * c ≠ xp + 8 * xc) (hx80 : 80 ≤ xl)
    {S1 : State} (hsp : S1.sp.toNat = s.sp.toNat - 176) (hg : S1.regs 28 = s.regs 28)
    (hF : MemFrame M S1.mem (winA s W 64)) (hreg : S1.mem.regions = s.mem.regions) :
    KPre R b1 L1 (W - 176) st p (2 * xl) c xp xl xc S1 := by
  obtain ⟨hce, hsw, hsv, hgl, hwt, hxlc, hxc40, hxl12, hxacc, hxh, hxw, hzc40, -, -, -, -, hstk, hxst, hlen, hcost,
    -⟩ := hJ.pre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hce1 := hJ.callee (stk1 := W - 176) (above1 := 48) hsp hg hF hreg (by omega) (by omega)
  obtain ⟨hst0, hstok, hstw, hstg, hsarr, hfg, hfw, hstf, hstwb, hfh⟩ := hstk
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩ := hce
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hFs : MemFrame s.mem S1.mem (R.rt ++ winA s W 64) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hpl := hJ.live
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hpl (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hpst := hJ.pst (by omega)
  have hpf := hJ.pfree (by omega)
  have hxw' := hxw (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  have hxs := hxst (by omega)
  have hgl' := hgl
  obtain ⟨-, -, -, -, -, -, -, -, -, hgw, -⟩ := hgl'
  simp only [win, outside_cons, outside_nil, and_true] at hpw hxw' hstw hfw hgw
  have hwin : ∀ a n, (a + n ≤ s.sp.toNat - W ∨ s.sp.toNat + 64 ≤ a) → Outside a n (win S1 (W - 176) 48) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hacc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hFs.accessible a n w
  have haccM : ∀ a n w, S1.mem.accessible a n w = M.accessible a n w := fun a n w => hF.accessible a n w
  have hfree : BasicSqr.freeP S1.mem st = BasicSqr.freeP s.mem st ∧
      BasicSqr.freeN S1.mem st = BasicSqr.freeN s.mem st := by
    simp only [BasicSqr.freeP, BasicSqr.freeN]; rw [eW, eL, eC]; exact ⟨rfl, rfl⟩
  have hsc : sqrC (stLen s.mem st) xl = makeB (2 * xl) + ksqrC (stLen s.mem st) xl := by
    unfold sqrC; rw [if_pos (by omega)]
  have hbud := hJ.bud
  refine ⟨hce1, by unfold sqrW at hsw; omega, hsv, globals_frame hgl hFs (by
      simp only [winA, outside_cons, outside_nil, and_true]; omega) fun a n h => by
      simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega,
    hwt, hx80, hxlc, hxc40, hxl12, by rw [hacc]; exact hxacc, hJ.ext.held hxh', hx48, hwin _ _ (by omega), rfl, hcap,
    hc40, fun _ => ⟨hp8, hph, by rw [haccM]; exact hpacc, hp48⟩, hwin _ _ (by omega), by show Apart _ _ ((S1.regs 28).toNat + 16) 8; rw [hg]; exact hpg, ?_, hpx,
    hna, ?_, ?_, by rw [eL]; exact hlen, by rw [eL]; omega, ?_⟩
  · show Apart st 24 p (8 * c) ∧ Apart p (8 * c) (BasicSqr.freeP S1.mem st) (BasicSqr.freeN S1.mem st)
    rw [hfree.1, hfree.2]; exact ⟨by unfold Apart at hpst ⊢; omega, hpf⟩
  · refine ⟨hst0, stkOK_frame hJ.stk hF (by simp only [winA, outside_cons, outside_nil, and_true]; omega),
      hwin _ _ (by omega), by show Apart _ _ ((S1.regs 28).toNat + 16) 8; rw [hg]; exact hstg, ?_,
      by show Apart _ _ ((S1.regs 28).toNat + 16) 8; rw [hfree.1, hfree.2, hg]; exact hfg,
      by rw [hfree.1, hfree.2]; exact hwin _ _ (by omega), by rw [hfree.1, hfree.2]; exact hstf, hstwb,
      by rw [hfree.1, hfree.2]; exact hJ.ext.held hfh⟩
    intro h; rw [eC] at h; obtain ⟨h1, h2⟩ := hsarr h
    simp only [win, outside_cons, outside_nil, and_true] at h1
    show _ ∧ Apart _ _ ((S1.regs 28).toNat + 16) 8
    rw [eW, eC, hg]; exact ⟨hwin _ _ (by omega), h2⟩
  · show Apart st 24 xp (8 * xl) ∧ Apart xp (8 * xl) (BasicSqr.freeP S1.mem st) (BasicSqr.freeN S1.mem st)
    rw [hfree.1, hfree.2]; exact hxs
  · show R.inv _ _ (S1.regs 28).toNat _; rw [hg]; exact inv_frame_winA hF hout0 (by omega) (by decide) hJ.inv


end FvModexp.Arm64.NatSqr
