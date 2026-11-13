import FvModexp.Proofs.Arm64.Exp.P2Q
import FvModexp.Proofs.Arm64.Exp.P2W2Pre
import FvModexp.Proofs.Arm64.Exp.NHyp

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the internal entry facts from a `NHyp.CPre`-form precondition (agent infra)

`PreC` is the exported-shape precondition (`NHyp.CPre` at `SP`, window `[SP - stk, SP + 96)`, inputs `x`, `y`, need
`2^13`, `x` odd, `y > 0`, `2 ≤ logM ≤ 2^13`, `0 < st`, `natOne`) used by the `expNNPowerOfTwo` dispatch; `epre_of`
gives `EPre` with frame `sp = SP - 464` and `K = stk - 464` (`[sp - K, sp + 560)` is the same window). Adapted from
the `nat.expNNEven` bridge `ExpEven.epre_of` (EvEP).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the `CPre`-form precondition (see the module doc) -/
@[reducible] def PreC (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (cst : Nat)
    (zp zl zc st xp xl yp yl lm : Nat) (s : State) : Prop :=
  NHyp.CPre R b L stk 96 zp zl zc st [(xp, xl), (yp, yl)] (2 ^ 13) cst s ∧
    natVal s.mem xp xl % 2 = 1 ∧ 0 < natVal s.mem yp yl ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧ 0 < st ∧
    ∃ op, EvenHyp.NatOne R L s.mem op (win s stk 96 ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      EvenHyp.StkApart s.mem st op 8

theorem ap_wC {a k SP stk : Nat} (h : Outside a k [(SP - stk, SP + 96)]) (h1 : 464 ≤ stk) (h2 : stk ≤ SP) :
    Apart a k (SP - 464 - (stk - 464)) (stk - 464 + 560) := by
  simp only [outside_cons, outside_nil, and_true] at h; unfold Apart; omega

theorem win_eqC {SP stk : Nat} (h1 : 464 ≤ stk) (h2 : stk ≤ SP) :
    [(SP - stk, SP + 96)] = [(SP - 464 - (stk - 464), SP - 464 + 560)] := by
  rw [show SP - 464 - (stk - 464) = SP - stk by omega, show SP - 464 + 560 = SP + 96 by omega]

theorem oe_ofC {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk st p n SP : Nat} (hS : s.sp.toNat = SP)
    (h1 : 464 ≤ stk) (h2 : stk ≤ SP)
    (h : ExpHyp.RdIn R L s stk 96 p n) (hst : Apart p (8 * n) st 24)
    (hf : Apart p (8 * n) (NHyp.freeOf s.mem st).1 (NHyp.freeOf s.mem st).2) :
    OE R L (SP - 464) (stk - 464) st s.mem p (8 * n) := by
  obtain ⟨-, -, -, hH, hw⟩ := h
  simp only [win, hS] at hw
  exact ⟨hH, ap_wC hw h1 h2, hst, hf⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the internal entry facts** -/
theorem epre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk cst : Nat}
    {zp zl zc st xp xl xc yp yl lm : Nat} {s : State}
    (hP : PreC R b L stk cst zp zl zc st xp xl yp yl lm s)
    (hk1 : 4768 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 464) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (hr : stkR (HW (stLen s.mem st) lm) s.mem st ≤ b) :
    EPre R (b - stkR (HW (stLen s.mem st) lm) s.mem st) L (stk - 464) (s.regs 28).toNat (s.sp.toNat - 464) st zp zc xp xl xc yp yl lm s := by
  obtain ⟨⟨hce, hsv, hgl, hro, hwT, hzl, hwo, hins, hsok, hstw, hstg, harr, hcap0, hneed, hwba, hstwb, hstf, hzs,
    hstgA, hfgA, hcst, hinv⟩, hX, hY, hlm2, hlm, hst0, op, hone, hsa⟩ := hP
  obtain ⟨hgd, hsok', hd, hwrt, hgw, hgrt, hLs, -⟩ := hce
  obtain ⟨hal, hle, h48, hacc⟩ := hsok'
  obtain ⟨g1, g2, g3⟩ := hgd
  generalize hS : s.sp.toNat = SP at *
  generalize hG : (s.regs 28).toNat = g at *
  have hspE : s.sp = BitVec.ofNat 64 (SP - 464 + 464) := by
    apply BitVec.eq_of_toNat_eq; rw [hS, BitVec.toNat_ofNat]; omega
  have hgE : s.regs 28 = BitVec.ofNat 64 g := by
    apply BitVec.eq_of_toNat_eq; rw [hG, BitVec.toNat_ofNat]; omega
  have ew := win_eqC (SP := SP) (by omega : 464 ≤ stk) hle
  have hy := hins yp yl (by simp)
  have hx := hins xp xl (by simp)
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  obtain ⟨hwo1, hwo2, hwo3⟩ := hwo
  simp only [win, hS] at hwrt hgw hLs hstw harr hwo3 hgl
  rw [ew] at hgl hLs
  refine ⟨⟨hspE, hgE, g1, g2, by omega, ?_, by omega, by omega, by omega, by omega, ?_, ?_, hLs, hd, hsv⟩,
    by omega, hgl, hro, hwT, hlm2, hlm, oe_ofC hS (by omega) hle hy.1 hy.2.2.2.1 hy.2.2.2.2.1, hy.1.2.1, hy.1.2.2.1,
    hy.2.2.1, hyl0, by have := hy.2.1; omega, oe_ofC hS (by omega) hle hx.1 hx.2.2.2.1 hx.2.2.2.2.1, hx.1.2.1,
    hx.1.2.2.1, hx.2.2.1, by have := hx.2.1; omega, by have := hx.1.2.2.1; omega, hxc, hzp, hwo1, fun hz => ?_, ?_,
    hsok, ap_wC hstw (by omega) hle, hstg, fun hc => ⟨ap_wC (harr hc).1 (by omega) hle, (harr hc).2⟩, hwba, hstwb,
    hstf, by omega, by omega, ⟨op, ?_, hsa⟩, P2Q.inv_eff hinv hr⟩
  · simp only [outside_cons] at hgw ⊢
    refine ⟨?_, hgrt⟩
    unfold Apart at hgw; omega
  · rw [show SP - 464 - (stk - 464) = SP - stk by omega, show stk - 464 + 560 = stk + 96 by omega]
    exact hacc
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only
    have := hwrt
    rwa [show SP - 464 + 560 - (SP - 464 - (stk - 464)) = stk - 464 + 560 by omega,
      show SP - 464 - (stk - 464) = SP - stk by omega, show stk - 464 + 560 = stk + 96 by omega]
  · obtain ⟨n1, n2, n3, n4⟩ := hwo2 hz
    obtain ⟨o1, o2⟩ := hwo3 hz
    rw [hG] at o2
    obtain ⟨z1, z2, z3⟩ := hzs hz
    exact ⟨⟨n2, ap_wC o1 (by omega) hle, z1, z2⟩, n3, n4, n1, o2.symm, hx.2.2.2.2.2 hz, hy.2.2.2.2.2 hz, z3⟩
  · obtain ⟨-, -, -, -, -, -, -, a8, a9, a10, -⟩ := hgl
    exact ⟨Or.inr a9, by simp only [outside_cons, outside_nil, and_true] at a10; unfold Apart; omega, hstgA.symm,
      hfgA.symm⟩
  · simp only [win, hS] at hone
    rw [show SP - 464 - (stk - 464) = SP - stk by omega, show SP - 464 + 560 = SP + 96 by omega]; exact hone

end FvModexp.Arm64.P2W2
