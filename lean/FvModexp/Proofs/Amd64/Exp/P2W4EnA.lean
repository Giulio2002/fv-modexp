import FvModexp.Proofs.Amd64.Exp.P2W4Defs
import FvModexp.Proofs.Amd64.Exp.P2W4Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` entry (amd64): entry → the `slices.Grow` decision (fn+0x0 .. fn+0x126) (agent top s48;
amd64 twin of `Arm64.P2W4.enA`, ported from agent divmc's amd64 `P2W2.enA`)

`enA`: stack-guard check, prologue (frame `0x2f8`), spills, defer record, `w = (logM+63) >> 6` (DX), `nr = rnd(20w) = 20w`
(BX); then either the join `enJ` (`len + nr ≤ cap`, no growth) or the entry of
`growslice(arr, len + nr, cap, len + nr - cap, Word)` (return `grRet`). Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- `LEAQ 0(DX)(DX*4), BX` (fn+0x81): `w + (w << 2) + 0 = 5w` -/
theorem lea5 (w : Nat) (hw : w ≤ 128) :
    BitVec.ofNat 64 w + BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (5 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]; omega

/-- `nr = rnd(20w)` (`SHLQ $2, BX; ADDQ $3, BX; ANDQ $-4, BX`, fn+0x85..0x91) -/
theorem nr20 (w : Nat) (hw : w ≤ 128) :
    (BitVec.ofNat 64 (5 * w) <<< 2 + 3#64) &&& BitVec.ofNat 64 18446744073709551612 = BitVec.ofNat 64 (20 * w) := by
  have e : BitVec.ofNat 64 (5 * w) <<< 2 = BitVec.ofNat 64 (20 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show 5 * w < 2 ^ 64 by omega)]; omega
  rw [e]
  have := StackNat.rnd_bv (BitVec.ofNat 64 (20 * w)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), rnd20] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enA {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp g st zp zl zc xp xl xc yp yl lm bp r w0 len0 cap0 : Nat} {M : Memory}
    (hal : sp % 8 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x358 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 8) 0x360 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 0x80)
    (hst1 : M.accessible st 24 false = true) (hst2 : st + 24 ≤ 2 ^ 48) (hstw : st + 24 ≤ sp ∨ sp + 0x358 ≤ st)
    (hw0 : M.readLE st 8 = w0) (hl0 : M.readLE (st + 8) 8 = len0) (hc0 : M.readLE (st + 16) 8 = cap0)
    (hl16 : len0 ≤ 2 ^ 16) (hc40 : cap0 < 2 ^ 40) (hlc : len0 ≤ cap0) (hlm : lm ≤ 2 ^ 13)
    (hzp : zp < 2 ^ 64) (hzl : zl < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hbp : bp < 2 ^ 64)
    (r2f8 : M.readLE (sp + 0x2f8) 8 = r) (r300 : M.readLE (sp + 0x300) 8 = yp) (r308 : M.readLE (sp + 0x308) 8 = yl)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x2f8)) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = BitVec.ofNat 64 lm) (h5 : S.regs 5 = BitVec.ofNat 64 bp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hx15 : S.xmm 15 = 0)
    (KJ : len0 + 20 * W lm ≤ cap0 → ∀ (S' : State) (M' : Memory),
      S'.rip = BitVec.ofNat 64 enJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = BitVec.ofNat 64 (sp + 0x2f0) →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 2 = BitVec.ofNat 64 (W lm) → S'.regs 3 = BitVec.ofNat 64 (20 * W lm) → S'.regs 12 = BitVec.ofNat 64 len0 →
      S'.regs 13 = BitVec.ofNat 64 cap0 →
      S'.regs 11 = BitVec.ofNat 64 w0 → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase = S.fsBase → S'.xmm 15 = 0 → S'.df = S.df →
      S'.mem = M' → MemFrame M M' [(sp, sp + 0x2f8), (sp + 0x318, sp + 0x358)] → M'.regions = M.regions →
      ESl M' sp st bp r zp zc xp xl xc yp yl lm len0 →
      ReachesRet (LibW.program.link impl) ret S' Q)
    (KG : cap0 < len0 + 20 * W lm → ∀ (S' : State) (M' : Memory),
      S'.rip = BitVec.ofNat 64 grE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 5 = BitVec.ofNat 64 (sp + 0x2f0) →
      S'.regs 0 = BitVec.ofNat 64 w0 → S'.regs 3 = BitVec.ofNat 64 (len0 + 20 * W lm) →
      S'.regs 1 = BitVec.ofNat 64 cap0 → S'.regs 7 = BitVec.ofNat 64 (len0 + 20 * W lm - cap0) →
      S'.regs 6 = BitVec.ofNat 64 wTy → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase = S.fsBase → S'.xmm 15 = 0 → S'.df = S.df →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 0x2f8), (sp + 0x318, sp + 0x358)] → M'.regions = M.regions →
      ESl M' sp st bp r zp zc xp xl xc yp yl lm len0 →
      M'.readLE (sp - 8) 8 = grRet →
      M'.readLE (sp + 0x100) 8 = W lm → M'.readLE (sp + 0xb8) 8 = 20 * W lm → M'.readLE (sp + 0xa8) 8 = len0 →
      M'.readLE (sp + 0xc0) 8 = len0 + 20 * W lm - cap0 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hsh := shr6 lm (by omega)
  have h5w := lea5 (W lm) (by omega)
  have hnr := nr20 (W lm) (by omega)
  have hgs : S.mem.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have e5 : BitVec.ofNat 64 (sp + 0x2f8) - 8#64 = BitVec.ofNat 64 (sp + 0x2f0) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e6 : BitVec.ofNat 64 (sp + 0x2f0) - 0x2f0#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hms := W2En.sub3_msb len0 (20 * W lm) cap0 (by omega) (by omega) (by omega) hlc
  have hzs := W2En.sub3_z len0 (20 * W lm) cap0 (by omega) (by omega) (by omega) hlc
  have m_bp : bp % 18446744073709551616 = bp := Nat.mod_eq_of_lt (by omega)
  have m_st : st % 18446744073709551616 = st := Nat.mod_eq_of_lt (by omega)
  have m_l0 : len0 % 18446744073709551616 = len0 := Nat.mod_eq_of_lt (by omega)
  have m_zp : zp % 18446744073709551616 = zp := Nat.mod_eq_of_lt (by omega)
  have m_zc : zc % 18446744073709551616 = zc := Nat.mod_eq_of_lt (by omega)
  have m_xp : xp % 18446744073709551616 = xp := Nat.mod_eq_of_lt (by omega)
  have m_xl : xl % 18446744073709551616 = xl := Nat.mod_eq_of_lt (by omega)
  have m_xc : xc % 18446744073709551616 = xc := Nat.mod_eq_of_lt (by omega)
  have m_lm : lm % 18446744073709551616 = lm := Nat.mod_eq_of_lt (by omega)
  have m_sa : (sp + 712) % 18446744073709551616 = (sp + 712) := Nat.mod_eq_of_lt (by omega)
  by_cases hk : len0 + 20 * W lm ≤ cap0
  · have hc3 : len0 + 20 * W lm < cap0 ∨ len0 + 20 * W lm = cap0 := by omega
    rcases hc3 with hc3 | hc3
    · have hms' : (BitVec.ofNat 64 (20 * W lm) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0)).msb =
          true := by rw [hms]; simp only [decide_eq_true_eq]; exact hc3
      have hzs' := hzs.trans (show (len0 + 20 * W lm = cap0) = False by
        simp only [eq_iff_iff, iff_false]; omega)
      refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 enJ) ?_
      janus64_run [hsh, h5w, hnr, hw0, hl0, hc0, e5, e6, hms', hzs'] until [enJ]
      refine KJ hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl
      case mf => janus_frame
      case sl =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, m_bp, m_st, m_l0,
          m_zp, m_zc, m_xp, m_xl, m_xc, m_lm, m_sa, r2f8, r300, r308]
      all_goals first | (janus64_simp; done) | skip
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals first | exact h7 | exact h14 | rfl
    · have hms' : (BitVec.ofNat 64 (20 * W lm) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0)).msb =
          false := by rw [hms]; simp only [decide_eq_false_iff_not]; omega
      have hzs' := hzs.trans (show (len0 + 20 * W lm = cap0) = True by simp only [eq_iff_iff, iff_true]; omega)
      refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 enJ) ?_
      janus64_run [hsh, h5w, hnr, hw0, hl0, hc0, e5, e6, hms', hzs'] until [enJ]
      refine KJ hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl
      case mf => janus_frame
      case sl =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, m_bp, m_st, m_l0,
          m_zp, m_zc, m_xp, m_xl, m_xc, m_lm, m_sa, r2f8, r300, r308]
      all_goals first | (janus64_simp; done) | skip
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals first | exact h7 | exact h14 | rfl
  · have hms' : (BitVec.ofNat 64 (20 * W lm) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0)).msb =
        false := by rw [hms]; simp only [decide_eq_false_iff_not]; omega
    have hzs' := hzs.trans (show (len0 + 20 * W lm = cap0) = False by simp only [eq_iff_iff, iff_false]; omega)
    have e9 : BitVec.ofNat 64 (20 * W lm) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0) =
        BitVec.ofNat 64 (len0 + 20 * W lm - cap0) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have e10 : BitVec.ofNat 64 cap0 + BitVec.ofNat 64 (len0 + 20 * W lm - cap0) =
        BitVec.ofNat 64 (len0 + 20 * W lm) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hlt : BitVec.ofNat 64 cap0 ≤ BitVec.ofNat 64 (len0 + 20 * W lm) := by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
    have hlt' : ¬ BitVec.ofNat 64 (len0 + 20 * W lm) ≤ BitVec.ofNat 64 cap0 := by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
    have hm9 : (BitVec.ofNat 64 (len0 + 20 * W lm - cap0)).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp only [decide_eq_false_iff_not]
      omega
    have hz9 : ((len0 + 20 * W lm - cap0) % 18446744073709551616 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have hz9' : (len0 + 20 * W lm - cap0 = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 grE) ?_
    janus64_run [hsh, h5w, hnr, hw0, hl0, hc0, e5, e6, hms', hzs', e9, e10, hlt, hlt', hm9, hz9, hz9'] until [grE]
    refine KG (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl ?q0 ?q1 ?q2 ?q3 ?q4
    case mf => janus_frame
    case sl =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, m_bp, m_st, m_l0,
        m_zp, m_zc, m_xp, m_xl, m_xc, m_lm, m_sa, r2f8, r300, r308]
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    all_goals first | exact h14 | omega |
      (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega) | rfl

end FvModexp.Amd64.P2W4
