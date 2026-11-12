import FvModexp.Proofs.Arm64.Nat.SqrNorm

/-!
# `nat.sqr` (arm64): facts for the scratch callees (`basicSqr`, `karatsubaSqr`) called at `SP - 176`

`Core.pg` (result apart from the guard word), `Core.hdrS` (stack header at the call state), `bs_pre` (`BasicSqr.Pre` at the
call of `basicSqr(stk, z[0:2n], x)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- the thresholds `basicSqrThreshold` (`= 12`) and `karatsubaSqrThreshold` (`= 80`) at `M` -/
theorem Core.thr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) :
    M.readLE 7147152 8 = 12 ∧ M.readLE 7147160 8 = 80 ∧ M.accessible 7147152 16 false = true := by
  obtain ⟨-, -, -, ⟨-, h12, h80, -, -, e12, e80, hacc, hrt, hw, -⟩, -⟩ := hJ.pre
  have eg : RunIface.gA = 7147136 := rfl
  rw [eg] at e12 e80 hacc hrt hw
  rw [e12] at h12; rw [e80] at h80
  simp only [win, outside_cons, outside_nil, and_true] at hw
  refine ⟨?_, ?_, ?_⟩
  · rw [hJ.rd (Or.inr (hrt.of_sub (by omega) (by omega)))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)]; exact h12
  · rw [hJ.rd (Or.inr (hrt.of_sub (by omega) (by omega)))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)]; exact h80
  · rw [hJ.F.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)

/-- `x` keeps its bytes from the entry to `M` -/
theorem Core.xv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hx : 0 < xl) :
    natVal M xp xl = natVal s.mem xp xl := by
  obtain ⟨-, -, -, -, -, hxlc, -, -, -, hxh, hxw, -⟩ := hJ.pre
  exact hJ.rd ((hxh (by omega)).1.sub (Nat.le_refl _) (by omega)) (hxw hx)

theorem Core.pg {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hc : 0 < c) :
    Apart p (8 * c) ((s.regs 28).toNat + 16) 8 := by
  obtain ⟨⟨-, -, -, -, -, hgr0, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hzg, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · exact (hzg hc).1
  · have := NatAdd.outside_of_inRanges hgr0 hin; unfold Apart; omega

/-- the result is apart from the stack's free part -/
theorem Core.pfree {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hc : 0 < c) :
    Apart p (8 * c) (BasicSqr.freeP s.mem st) (BasicSqr.freeN s.mem st) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hzs, -, ⟨-, -, -, -, -, -, -, -, -, hfh, -⟩, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, hap, -⟩
  · exact (hzs hc).2.2.1
  · exact apart_of_held hfh hin hap

/-- the result is apart from the threshold globals -/
theorem Core.pgA {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hc : 0 < c) : Apart p (8 * c) RunIface.gA 32 := by
  obtain ⟨-, -, -, ⟨-, -, -, -, -, -, -, -, hgrt, -⟩, -, -, -, -, -, -, -, -, -, -, hzs, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · exact (hzs hc).2.2.2
  · have := NatAdd.outside_of_inRanges hgrt hin; unfold Apart; omega

theorem Apart.subL {a n m b k : Nat} (h : Apart a n b k) (hm : m ≤ n) : Apart a m b k := by
  unfold Apart at h ⊢; omega

/-- the stack header at a state reached from `M` by window stores -/
theorem Core.hdrS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) {m : Memory} (hF : MemFrame M m (winA s W 64)) :
    stW m st = stW s.mem st ∧ stLen m st = stLen s.mem st ∧ stCap m st = stCap s.mem st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hJ.pre
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have e : ∀ k, k + 8 ≤ 24 → m.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk => by
    rw [hF.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega), hJ.hdr k hk]
  have e0 := e 0 (by omega); simp only [Nat.add_zero] at e0
  exact ⟨e0, e 8 (by omega), e 16 (by omega)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `BasicSqr.Pre` at the call of `basicSqr(stk, z[0:2n], x)` (`12 ≤ n`) -/
theorem bs_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hpx : Apart p (8 * c) xp (8 * xl)) (hx12 : 12 ≤ xl)
    {S1 : State} (hsp : S1.sp.toNat = s.sp.toNat - 176) (hg : S1.regs 28 = s.regs 28)
    (hF : MemFrame M S1.mem (winA s W 64)) (hreg : S1.mem.regions = s.mem.regions) :
    BasicSqr.Pre R b1 L1 st p (2 * xl) c xp xl S1 := by
  have hce1 := hJ.callee (stk1 := 4432) (above1 := 64) hsp hg hF hreg (by
    obtain ⟨-, hsw, -⟩ := hJ.pre; unfold sqrW ksqrW at hsw; omega) (by omega)
  obtain ⟨hce, hsw, hsv, hgl, -, hxlc, hxc40, hxl12, hxacc, hxh, hxw, hzc40, -, -, -, -, hstk, hxst, hlen, hcost,
    -⟩ := hJ.pre
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, hstok, hstw, hstg, hsarr, hfg, hfw, hstf, hstwb, -⟩ := hstk
  obtain ⟨-, hb12, -, -, -, e16, -, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := hgl
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩ := hce
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hFs : MemFrame s.mem S1.mem (R.rt ++ winA s W 64) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hpst := hJ.pst (by omega)
  have hpf := hJ.pfree (by omega)
  have hxw' := hxw (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  have hxs := hxst (by omega)
  have eg : RunIface.gA = 7147136 := rfl
  rw [eg] at e16 hgacc hgrt hgw
  rw [e16] at hb12
  have eA : BasicSqr.thrA = 7147152 := rfl
  simp only [win, outside_cons, outside_nil, and_true] at hpw hxw' hstw hfw hgw hwbw
  have hwin : ∀ a n, (a + n ≤ s.sp.toNat - W ∨ s.sp.toNat + 64 ≤ a) → Outside a n (win S1 4432 64) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hacc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hFs.accessible a n w
  have haccM : ∀ a n w, S1.mem.accessible a n w = M.accessible a n w := fun a n w => hF.accessible a n w
  have hfree : BasicSqr.freeP S1.mem st = BasicSqr.freeP s.mem st ∧
      BasicSqr.freeN S1.mem st = BasicSqr.freeN s.mem st := by
    simp only [BasicSqr.freeP, BasicSqr.freeN]; rw [eW, eL, eC]; exact ⟨rfl, rfl⟩
  have hkc : stackNatCost (stLen s.mem st) (2 * xl) ≤ ksqrC (stLen s.mem st) xl := by
    by_cases h : 80 ≤ xl
    · rw [ksqrC_big h]; omega
    · rw [ksqrC_small (by omega)]; exact Nat.le_refl _
  have hsc : sqrC (stLen s.mem st) xl = makeB (2 * xl) + ksqrC (stLen s.mem st) xl := by
    unfold sqrC; rw [if_pos hx12]
  have hbud := hJ.bud
  refine ⟨hce1, hsv, ?_, ?_, ?_, by omega, rfl, hcap, hc40, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eA, hacc]; exact Memory.accessible_mono _ hgacc (by omega) (by omega)
  · rw [eA, hFs.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgrt.of_sub (by omega) (by omega), by omega, by omega⟩)]; exact hb12
  · rw [eA]; exact hwin _ _ (by omega)
  · intro _; exact ⟨hp8, hph.sub (Nat.le_refl _) (by omega),
      by rw [haccM]; exact Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega), by omega⟩
  · exact hwin _ _ (by omega)
  · rw [hg]; exact Apart.subL hpg (by omega)
  · rw [hacc]; exact hxacc
  · exact hJ.ext.held (hxh'.sub (Nat.le_refl _) (by omega))
  · exact hwin _ _ (by omega)
  · exact Apart.subL hpx (by omega)
  · exact stkOK_frame hJ.stk hF (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  · exact hwin _ _ (by omega)
  · rw [hg]; exact hstg
  · intro h; rw [eC] at h; obtain ⟨h1, h2⟩ := hsarr h
    simp only [win, outside_cons, outside_nil, and_true] at h1
    rw [eW, eC, hg]; exact ⟨hwin _ _ (by omega), h2⟩
  · rw [hfree.1, hfree.2, hg]; exact hfg
  · rw [eL]; omega
  · unfold Apart at hpst ⊢; omega
  · exact hxs.1
  · rw [hfree.1, hfree.2]; exact ⟨Apart.subL hpf (by omega), hxs.2.1⟩
  · rw [hfree.1, hfree.2]; exact hstf
  · rw [hfree.1, hfree.2]; exact hwin _ _ (by omega)
  · rw [eL]; show stackNatCost _ _ ≤ _; omega
  · rw [hg]; exact inv_frame_winA hF hout0 (by omega) (by decide) hJ.inv
  · rw [hacc]; exact hwbacc
  · exact hstwb

end FvModexp.Arm64.NatSqr
