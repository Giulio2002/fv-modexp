import FvModexp.Proofs.Arm64.Exp.EvPre

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the internal entry facts from the exported precondition (agent infra)

`epre_of`: `ExpEven.Pre` (the `NHyp.CPre` form at `SP`, window `[SP - stk, SP + 112)`) gives `EPre` with frame
`sp = SP - 336` and `K = stk - 336` (so `[sp - K, sp + 448)` is the same window). The capacities `xc`/`yc`/`mc` and
`zp` (unconstrained by the exported pre when `zc = 0`) enter as words (`< 2^64`); the composition passes their
register values.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- an `Outside` the window fact as `Apart` from the internal window -/
theorem ap_w {a k SP stk : Nat} (h : Outside a k [(SP - stk, SP + 112)]) (h1 : 336 ≤ stk) (h2 : stk ≤ SP) :
    Apart a k (SP - 336 - (stk - 336)) (stk - 336 + 448) := by
  simp only [outside_cons, outside_nil, and_true] at h; unfold Apart; omega

theorem win_eq {SP stk : Nat} (h1 : 336 ≤ stk) (h2 : stk ≤ SP) :
    [(SP - stk, SP + 112)] = [(SP - 336 - (stk - 336), SP - 336 + 448)] := by
  rw [show SP - 336 - (stk - 336) = SP - stk by omega, show SP - 336 + 448 = SP + 112 by omega]

/-- an input operand of the exported pre as an entry object -/
theorem oe_of {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk st p n SP : Nat} (hS : s.sp.toNat = SP)
    (h1 : 336 ≤ stk) (h2 : stk ≤ SP)
    (h : ExpHyp.RdIn R L s stk 112 p n) (hst : Apart p (8 * n) st 24)
    (hf : Apart p (8 * n) (NHyp.freeOf s.mem st).1 (NHyp.freeOf s.mem st).2) :
    OE R L (SP - 336) (stk - 336) st s.mem p (8 * n) := by
  obtain ⟨-, -, -, hH, hw⟩ := h
  simp only [win, hS] at hw
  exact ⟨hH, ap_w hw h1 h2, hst, hf⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the internal entry facts** -/
theorem epre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk : Nat} {need : Nat → Nat → Nat → Nat}
    {cost : Nat → Nat → Nat → Nat → Nat} {zp zl zc st xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    (hP : Pre R b L stk 112 need cost zp zl zc st xp xl yp yl mp ml s)
    (hk1 : 4640 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 336) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) (hyc : yc < 2 ^ 64)
    (hmc : mc < 2 ^ 64) :
    EPre R b L (stk - 336) (s.regs 28).toNat (s.sp.toNat - 336) st zp zc xp xl xc yp yl yc mp ml mc s := by
  obtain ⟨⟨hce, hsv, hgl, hro, hwT, hzl, hwo, hins, hsok, hstw, hstg, harr, hcap0, hneed, hwba, hstwb, hstf, hzs,
    hstgA, hfgA, hcst, hinv⟩, hX, hY, hM, hMe, hxl, hml, hst0, op, hone, hsa⟩ := hP
  obtain ⟨hgd, hsok', hd, hwrt, hgw, hgrt, hLs, -⟩ := hce
  obtain ⟨hal, hle, h48, hacc⟩ := hsok'
  obtain ⟨g1, g2, g3⟩ := hgd
  generalize hS : s.sp.toNat = SP at *
  generalize hG : (s.regs 28).toNat = g at *
  have hspE : s.sp = BitVec.ofNat 64 (SP - 336 + 336) := by
    apply BitVec.eq_of_toNat_eq; rw [hS, BitVec.toNat_ofNat]; omega
  have hgE : s.regs 28 = BitVec.ofNat 64 g := by
    apply BitVec.eq_of_toNat_eq; rw [hG, BitVec.toNat_ofNat]; omega
  have ew := win_eq (SP := SP) (by omega : 336 ≤ stk) hle
  have hy := hins yp yl (by simp)
  have hx := hins xp xl (by simp)
  have hm := hins mp ml (by simp)
  have hml0 : 0 < ml := by
    rcases Nat.eq_zero_or_pos ml with h | h
    · subst h; simp [natVal] at hM
    · exact h
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  obtain ⟨hwo1, hwo2, hwo3⟩ := hwo
  simp only [win, hS] at hwrt hgw hLs hstw harr hwo3 hgl
  rw [ew] at hgl hLs
  refine ⟨⟨hspE, hgE, g1, g2, by omega, ?_, by omega, by omega, by omega, by omega, ?_, ?_, hLs, hd, hsv⟩,
    by omega, hgl, hro, hwT, hml0, hml, oe_of hS (by omega) hle hy.1 hy.2.2.2.1 hy.2.2.2.2.1, hy.1.2.1, hy.1.2.2.1,
    hy.2.2.1, hyl0, hy.2.1, oe_of hS (by omega) hle hx.1 hx.2.2.2.1 hx.2.2.2.2.1, hx.1.2.1, hx.1.2.2.1, hx.2.2.1,
    hxl, by have := hx.1.2.2.1; omega, hxc, hzp, hwo1, fun hz => ?_, ?_, hsok, ap_w hstw (by omega) hle, hstg,
    fun hc => ⟨ap_w (harr hc).1 (by omega) hle, (harr hc).2⟩, hwba, hstwb, hstf, by omega, by omega,
    ⟨op, ?_, hsa⟩, ⟨oe_of hS (by omega) hle hm.1 hm.2.2.2.1 hm.2.2.2.2.1, hm.1.2.1, hm.1.2.2.1, hm.2.2.1,
      hm.2.2.2.2.2, by have := hy.1.2.2.1; omega, hyc, by have := hm.1.2.2.1; omega, hmc, hcap0⟩, hinv⟩
  · simp only [outside_cons] at hgw ⊢
    refine ⟨?_, hgrt⟩
    unfold Apart at hgw; omega
  · rw [show SP - 336 - (stk - 336) = SP - stk by omega, show stk - 336 + 448 = stk + 112 by omega]
    exact hacc
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only
    have := hwrt
    rwa [show SP - 336 + 448 - (SP - 336 - (stk - 336)) = stk - 336 + 448 by omega,
      show SP - 336 - (stk - 336) = SP - stk by omega, show stk - 336 + 448 = stk + 112 by omega]
  · obtain ⟨n1, n2, n3, n4⟩ := hwo2 hz
    obtain ⟨o1, o2⟩ := hwo3 hz
    rw [hG] at o2
    obtain ⟨z1, z2, z3⟩ := hzs hz
    exact ⟨⟨n2, ap_w o1 (by omega) hle, z1, z2⟩, n3, n4, n1, o2.symm, hx.2.2.2.2.2 hz, hy.2.2.2.2.2 hz, z3⟩
  · obtain ⟨-, -, -, -, -, -, -, a8, a9, a10, -⟩ := hgl
    exact ⟨Or.inr a9, by simp only [outside_cons, outside_nil, and_true] at a10; unfold Apart; omega, hstgA.symm,
      hfgA.symm⟩
  · simp only [win, hS] at hone
    rw [show SP - 336 - (stk - 336) = SP - stk by omega, show SP - 336 + 448 = SP + 112 by omega]; exact hone

end FvModexp.Arm64.ExpEven
