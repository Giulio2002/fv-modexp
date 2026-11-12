import FvModexp.Proofs.Arm64.Exp.P2W2Defs

/-!
# `expNNPowerOfTwoWindowSize2` entry (arm64): entry → the `slices.Grow` decision (fn+0x0 .. fn+0xe4) (agent infra)

`enA`: guard, prologue (frame 464), defer record, argument spills, `w = (logM+63) >> 6`, `nr = rnd(8w) = 8w`; then either
the join `enJ` (`len + nr ≤ cap`, no growth) or the entry of `growslice(arr, len + nr, cap, len + nr - cap, Word)`
(return `grRet`). Continuation form. Adapted from agent expmc's window-2 `W2En.enA`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enA (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop)
    (sp g st zp zl zc xp xl xc yp yl yc lm ret w0 len0 cap0 : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 560 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 8) 568 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 128)
    (hst1 : M.accessible st 24 false = true) (hst2 : st + 24 ≤ 2 ^ 48) (hstw : st + 24 ≤ sp - 8 ∨ sp + 560 ≤ st)
    (hw0 : M.readLE st 8 = w0) (hl0 : M.readLE (st + 8) 8 = len0) (hc0 : M.readLE (st + 16) 8 = cap0)
    (hl16 : len0 ≤ 2 ^ 16) (hc40 : cap0 < 2 ^ 40) (hlm : lm ≤ 2 ^ 13) (hret48 : ret < 2 ^ 48)
    (hzp : zp < 2 ^ 64) (hzl : zl < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hyp : yp < 2 ^ 64) (hyl : yl < 2 ^ 64) (hyc : yc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnE) (hsp : S.sp = BitVec.ofNat 64 (sp + 464))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 lm)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (KJ : len0 + 8 * W lm ≤ cap0 → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 enJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 11 = BitVec.ofNat 64 (W lm) →
      S'.regs 13 = BitVec.ofNat 64 w0 → S'.regs 14 = BitVec.ofNat 64 len0 →
      S'.regs 12 = BitVec.ofNat 64 cap0 → S'.regs 9 = BitVec.ofNat 64 (len0 + 8 * W lm) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 456), (sp + 472, sp + 560)] → M'.regions = M.regions →
      ESl M' sp st r29 ret zp zc xp xl xc yp yl lm len0 →
      ReachesRet (LibExp.program.link impl) ret0 S' Q)
    (KG : cap0 < len0 + 8 * W lm → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 grE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 w0 → S'.regs 1 = BitVec.ofNat 64 (len0 + 8 * W lm) →
      S'.regs 2 = BitVec.ofNat 64 cap0 → S'.regs 3 = BitVec.ofNat 64 (len0 + 8 * W lm - cap0) →
      S'.regs 4 = BitVec.ofNat 64 wTy → S'.regs 30 = BitVec.ofNat 64 grRet →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 456), (sp + 472, sp + 560)] → M'.regions = M.regions →
      ESl M' sp st r29 ret zp zc xp xl xc yp yl lm len0 →
      M'.readLE (sp + 240) 8 = len0 + 8 * W lm → M'.readLE (sp + 176) 8 = len0 →
      M'.readLE (sp + 192) 8 = len0 + 8 * W lm - cap0 → M'.readLE (sp + 232) 8 = cap0 →
      M'.readLE (sp + 248) 8 = W lm →
      ReachesRet (LibExp.program.link impl) ret0 S' Q) :
    ReachesRet (LibExp.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KJ KG
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hsh := shr6 lm (by omega)
  have hadd : BitVec.ofNat 64 lm + 63#64 = BitVec.ofNat 64 (lm + 63) := (BitVec.ofNat_add lm 63).symm
  have h63 : (BitVec.ofNat 64 (8 * W lm)).getLsbD 63 = false :=
    getLsbD63_false _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  have e5 : BitVec.ofNat 64 len0 + BitVec.ofNat 64 (8 * W lm) = BitVec.ofNat 64 (len0 + 8 * W lm) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hti := toInt_sub3 len0 (8 * W lm) cap0 (by omega) (by omega) (by omega)
  rw [e5] at hti
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 464) - 464#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs8 : sp - 8 + 8 = sp := by omega
  have es2 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hnr := nr8 (W lm) (by omega)
  by_cases hk : len0 + 8 * W lm ≤ cap0
  · janus_run [es1, es2, hadd, TruncMath.rot6, hsh, hnr, h63, e5, hti, hw0, hl0, hc0] until [enJ]
    refine KJ hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 456)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 472, sp + 560)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    case sl =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := omega) only [hs8, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      all_goals first | omega | skip
    all_goals first | (janus_simp; done) | skip
  · have e3 : BitVec.ofNat 64 (len0 + 8 * W lm) - BitVec.ofNat 64 cap0 =
        BitVec.ofNat 64 (len0 + 8 * W lm - cap0) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have e1 : BitVec.ofNat 64 cap0 + BitVec.ofNat 64 (len0 + 8 * W lm - cap0) =
        BitVec.ofNat 64 (len0 + 8 * W lm) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    janus_run [es1, es2, hadd, TruncMath.rot6, hsh, hnr, h63, e5, hti, e3, e1, hw0, hl0, hc0] until [grE]
    refine KG (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl ?q1 ?q2 ?q3 ?q4 ?q5
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 456)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 472, sp + 560)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    case sl =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := omega) only [hs8, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      all_goals first | omega | skip
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals omega

end FvModexp.Arm64.P2W2
