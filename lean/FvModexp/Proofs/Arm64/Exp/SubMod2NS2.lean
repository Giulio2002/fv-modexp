import FvModexp.Proofs.Arm64.Exp.SubMod2NSeg
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

/-!
# `nat.subMod2N` (arm64): `J1` → `J2` (agent infra)

`y.bitLen()` (inline), and when it exceeds `n`, `y = nat(nil).trunc(y, n)` (`alias(z, y)` is false: `y`'s array is
apart from `z`'s; `TruncHyp` with `z = nil`, so the result is a fresh array).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- `J2` reached with `y' = y` (no truncation: `Y < 2^n`) after the stores of the `x'` locals -/
theorem j2_skip {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k2 : J2 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    {M : Memory} {l1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : Rt R b L s zp zc n 1 M L1 b1)
    (hv : natVal M zp l1 = natVal s.mem zp zl % 2 ^ n) (hnorm : NatNorm M zp l1) (hlc : l1 ≤ zc)
    (S : State) (hF : MemFrame M S.mem (winA s K A)) (hreg : S.mem.regions = M.regions)
    (hpc : S.pc = BitVec.ofNat 64 (1805584 + 0x1c8)) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18)
    (h3 : S.regs 3 = BitVec.ofNat 64 zp) (h4 : S.regs 4 = BitVec.ofNat 64 l1) (h5 : S.regs 5 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (hfw : Fw s S.mem zp zl zc yp n) (r16 : S.mem.readLE (s.sp.toNat - 16) 8 = zp)
    (r40 : S.mem.readLE (s.sp.toNat - 40) 8 = l1) (r32 : S.mem.readLE (s.sp.toNat - 32) 8 = zc)
    (hyv : natVal s.mem yp yl < 2 ^ n) :
    Goal impl R b L zp zl zc yp yl n s S := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨-, -, -, hw⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, hyl, hyc, -, -, hzw, -, -, hya, hy48,
    hyh, hyw, hyn, hzy, -⟩ := hpre'
  have hrt' := rt_mono (rt_stk hpre (hrt) hF hreg) (show 1 ≤ 2 by omega)
  have hzw' : Outside zp (8 * l1) (winA s K A) := by
    simp only [win, winA, K, A, outside_cons, outside_nil, and_true] at hzw ⊢; omega
  have hywA : Outside yp (8 * yl) (winA s K A) := by
    simp only [win, winA, K, A, outside_cons, outside_nil, and_true] at hyw ⊢; omega
  have hzyl : Apart yp (8 * yl) zp (8 * zc) := by unfold Apart at hzy ⊢; omega
  have hvy : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hrt' hyh hywA hzyl
  have hyn' : NatNorm S.mem yp yl := by
    rcases hyn with h | h
    · exact Or.inl h
    rcases Nat.eq_zero_or_pos yl with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    rw [rd_held hrt' (hyh.sub (by omega) (by omega)) (hywA.of_sub (by omega) (by omega))
      (by unfold Apart at hzyl ⊢; omega)]
    exact h
  have hxl := len_le_W hnorm (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  refine k2 S _ yp yl yc L1 b1 hpre hpc hsp h28 h18 h3 h4 h5 h6 h7 h8 hfw r16 r40 r32 hrt' ?_ ?_ hxl ?_ ?_ ?_ hyl
    (by omega) ?_ hy48 (hrt.2.2.2.1.held hyh) ?_ (by unfold Apart at hzy ⊢; omega)
  · rw [natVal_frame hF hzw', hv]
  · exact natNorm_frame hF hzw' hnorm
  · rw [hvy, Nat.mod_eq_of_lt hyv]
  · exact hyn'
  · exact len_le_W hyn' (by rw [hvy]; exact hyv)
  · rw [hF.accessible, hrt.2.1.accessible]; exact hya
  · simp only [win, K, A, outside_cons, outside_nil, and_true] at hyw; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `y = nat(nil).trunc(y, n)` returns (at `+0x1b0`): reload `x'`, move the result to `X6..X8`, `J2` -/
theorem s2t (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k2 : J2 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (M0 : Memory) {l1 : Nat} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt0 : Rt R b L s zp zc n 1 M0 L1 b1)
    (hfw0 : Fw s M0 zp zl zc yp n) (r16 : M0.readLE (s.sp.toNat - 16) 8 = zp)
    (r40 : M0.readLE (s.sp.toNat - 40) 8 = l1) (r32 : M0.readLE (s.sp.toNat - 32) 8 = zc)
    (hv0 : natVal M0 zp l1 = natVal s.mem zp zl % 2 ^ n) (hn0 : NatNorm M0 zp l1) (hlc : l1 ≤ zc) (hy1 : 1 ≤ yl)
    (hyv0 : natVal M0 yp yl = natVal s.mem yp yl)
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : S0.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h280 : S0.regs 28 = s.regs 28)
    (s' : State) (hpc' : s'.pc = BitVec.ofNat 64 (1805584 + 4 * 108)) (hsp' : s'.sp = S0.sp)
    (h28' : s'.regs 28 = S0.regs 28) (h18' : s'.regs 18 = s.regs 18) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b1 L1 stkT aboveT 0 0 yp yl n S0 s') :
    Goal impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨⟨-, -, -⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩, -, -, -, -, -, -, -, hzl, hW, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  simp only [W] at hW
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv, hnorm, hlc', hc40, hlive, -, hfresh⟩, hcap, ⟨hLE, hbud, hinv⟩, hF, hLF⟩ :=
    hpost
  have hneed : 0 < truncNeed yl n := by unfold truncNeed; have := hpre.2.2.2.2.2.1; omega
  have hc1 : truncNeed yl n ≤ c' := hcap hneed
  obtain ⟨hIn, hAp⟩ := hfresh hneed (by omega)
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hlive (by omega)
  have hspT : S0.sp.toNat = s.sp.toNat - 144 := by rw [hsp0]; exact tN (by omega)
  simp only [winA, hspT] at hF
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hacc' : s'.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by
    rw [hF.accessible, hS0, hrt0.2.1.accessible]; exact hw
  have rd : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 88 → (a + 8 ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 56 ≤ a) →
      s'.mem.readLE a 8 = M0.readLE a 8 := by
    intro a h1 h2 h3
    rw [← hS0]
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw0
  have q16 := (rd (s.sp.toNat - 16) (by omega) (by omega) (by omega)).trans r16
  have q40 := (rd (s.sp.toNat - 40) (by omega) (by omega) (by omega)).trans r40
  have q32 := (rd (s.sp.toNat - 32) (by omega) (by omega) (by omega)).trans r32
  have hsp'' : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) := hsp'.trans hsp0
  have hzh : Held R L1 zp (8 * zc) := (hrt0.2.2.2.2.2.2 (by omega)).2.1
  have hzh1 : Held R L1 zp (8 * l1) := hzh.sub (Nat.le_refl _) (by omega)
  have hrt1 : Rt R b L s zp zc n 2 s'.mem L' b' := by
    rw [hS0] at hF hreg' hLF
    rw [h280] at hinv
    refine rt_call hrt0 (by omega) hkT (by omega) (Or.inr rfl) hreg' hF hLF hLE hbud (truncNeed_le_w _ _) hinv ?_
    intro hc
    obtain ⟨z1, z2, z3, z4⟩ := hrt0.2.2.2.2.2.2 hc
    exact ⟨z1, hLE.held z2, by rw [hF.accessible]; exact z3, z4⟩
  have hzr : ∀ a m, zp ≤ a → a + m ≤ zp + 8 * l1 → s'.mem.readLE a m = M0.readLE a m := by
    intro a m h1 h2
    rw [← hS0]
    refine Expmc.held_readLE (hzh1.sub h1 h2) hF hLF ?_ (by simp only [outside_cons, outside_nil, and_true]; omega)
    simp only [outside_cons, outside_nil, and_true]; omega
  have hzx : natVal s'.mem zp l1 = natVal M0 zp l1 := hzr _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hzn : NatNorm s'.mem zp l1 := by
    rcases hn0 with h | h
    · exact Or.inl h
    rcases Nat.eq_zero_or_pos l1 with h0 | h0
    · exact Or.inl h0
    exact Or.inr (by rw [hzr _ _ (by omega) (by omega)]; exact h)
  obtain ⟨rr, hrr, hr1, hr2⟩ := id hIn
  have hrro := MemFrame.outside_mem hout hrr
  unfold Goal
  janus_run [q16, q40, q32] until [1806040]
  refine k2 _ l1 p' l' c' L' b' hpre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrt1 ?_ ?_ ?_ ?_ ?_ ?_ hlc' hc40 ?_ ?_ ?_ ?_ ?_
  all_goals try janus_simp
  · rw [show BitVec.toNat s.sp - 144 + 128 = BitVec.toNat s.sp - 16 by omega, r16]
  · rw [show BitVec.toNat s.sp - 144 + 104 = BitVec.toNat s.sp - 40 by omega, r40]
  · rw [show BitVec.toNat s.sp - 144 + 112 = BitVec.toNat s.sp - 32 by omega, r32]
  · exact ⟨(rd _ (by omega) (by omega) (by omega)).trans f1, (rd _ (by omega) (by omega) (by omega)).trans f2,
      (rd _ (by omega) (by omega) (by omega)).trans f3, (rd _ (by omega) (by omega) (by omega)).trans f4,
      (rd _ (by omega) (by omega) (by omega)).trans f5, (rd _ (by omega) (by omega) (by omega)).trans f6,
      (rd _ (by omega) (by omega) (by omega)).trans f7⟩
  · exact r16
  · exact r40
  · exact r32
  · exact hv0
  · exact hzn
  · exact len_le_W hn0 (by rw [hv0]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  · rw [hv, hS0, hyv0]
  · exact hnorm
  · exact len_le_W hnorm (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  · rw [← hS0, ← hF.accessible]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  · omega
  · exact hph.sub (Nat.le_refl _) (by omega)
  · omega
  · have := apart_fresh hzh hAp hIn; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (k2 : J2 impl R b L op zp zl zc yp yl yc n s) : J1 impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 L1 b1 hpre hpc hsp h28 h18 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hfw hrt hv hnorm hlc
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, hzg, -, hya, hy48, hyh, hyw, hyn, hzy, -⟩ := hpre'
  simp only [W] at hW
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout hyw
  simp only [K, A] at hw hout hzw hg3 hb' ha hga hyw
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hya' : S.mem.accessible yp (8 * yl) false = true := by rw [hrt.2.1.accessible]; exact hya
  have hywA : Outside yp (8 * yl) (winA s K A) := by
    simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
  have hzyl : Apart yp (8 * yl) zp (8 * zc) := by unfold Apart at hzy ⊢; omega
  have hyv : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hrt hyh hywA hzyl
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    refine hrt.2.1.readLE _ _ ?_
    simp only [winA, K, A, outside_append, outside_cons, outside_nil, and_true]
    unfold Apart at hga hzg
    exact ⟨⟨hpre.1.2.2.2.2.2.1, by omega, by omega⟩, by omega⟩
  unfold Goal
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw
  by_cases hy0 : yl = 0
  · subst hy0
    janus_run until [1806040]
    refine j2_skip k2 hpre hrt hv hnorm hlc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [winA, K, A]; janus_frame
    all_goals try janus_simp
    · refine fw_loc (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_
      janus_frame
    · exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.one_le_two_pow)

  have hyt : S.mem.readLE (yp + 8 * (yl - 1)) 8 = s.mem.readLE (yp + 8 * (yl - 1)) 8 :=
    rd_held hrt (hyh.sub (by omega) (by omega)) (hywA.of_sub (by omega) (by omega)) (by unfold Apart at hzyl ⊢; omega)
  have e1 : (yp + 8 * (18446744073709551615 + yl)) % 18446744073709551616 = yp + 8 * (yl - 1) := by omega
  have h63 : (BitVec.ofNat 64 yl - 1#64).getLsbD 63 = false := by
    have e : (BitVec.ofNat 64 yl - 1#64).toNat = yl - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    show (BitVec.ofNat 64 yl - 1#64).toNat.testBit 63 = false
    rw [e]; exact Nat.testBit_lt_two_pow (by omega)
  janus_run [e1, h63] until [1805848]
  generalize hxd : BitVec.ofNat 64 (S.mem.readLE (yp + 8 * (yl - 1)) 8) = x
  janus_run until [1805872]
  gen_reg 11 as t with hT
  janus_run until [1805888]
  gen_reg 10 as bl with hBl
  have hbl : bl.toNat = 64 * (yl - 1) + Aux.bitLen (s.mem.readLE (yp + 8 * (yl - 1)) 8) := by
    rw [← hBl, ← hT, ← BitLenA64.smearBV, BitLenA64.clz_smear, ← hxd, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Util.readLE8_lt _ _), hyt]
    exact BitLenA64.bl_exact _ _ (Util.readLE8_lt _ _) (by omega) (by omega)
  by_cases hc : bl.toNat ≤ n
  · janus_run [hc] until [1806040]
    refine j2_skip k2 hpre hrt hv hnorm hlc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [winA, K, A]; janus_frame
    all_goals try janus_simp
    · refine fw_loc (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_
      janus_frame
    · refine Nat.lt_of_lt_of_le (BitLenA64.natVal_lt_bl _ _ _ (by omega)) (Nat.pow_le_pow_right (by omega) ?_)
      omega

  · have e2 : (zp + 8 * (18446744073709551615 + zc)) % 18446744073709551616 = zp + 8 * (zc - 1) := by omega
    have e3 : (yp + 8 * (18446744073709551615 + yc)) % 18446744073709551616 = yp + 8 * (yc - 1) := by omega
    have hzy' := hzy
    unfold Apart at hzy'
    janus_run [hc, e2, e3] until [1786000]
    all_goals
      have hzw' : Outside zp (8 * l1) (winA s K A) := by
        simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
      refine truncCall hap hns htr (zp := 0) (zl := 0) (zc := 0) (x := yp) (xl := yl) (xc := yc) (n := n)
        (ra_of hap hnf 108 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
        (truncPre_of hpre (rt_stk hpre hrt ?_ ?_) (by omega) rfl ?_ ?_ hkT haT (Or.inr rfl) (Nat.le_refl _) (by omega) ?_
          hy48 (hrt.2.2.2.1.held hyh) (by omega) (by omega) (Or.inr fun h => absurd h (by omega)))
        (Or.inr (by have := bitLen_le64 (s.mem.readLE (yp + 8 * (yl - 1)) 8) (Util.readLE8_lt _ _); omega))
        (Or.inr (Or.inr ⟨by omega, by omega⟩))
        fun s' hpc' hsp' h28' h29' h18' hreg' hpost => ?qK
      case qK =>
        refine s2t impl k2 hpre hkT haT _ (rt_stk hpre hrt ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ hlc (by omega) ?_ _ rfl ?_ ?_ s'
          hpc' hsp' h28' ?_ hreg' hpost
        · simp only [winA, K, A]; janus_frame
        · janus_simp
        · refine fw_loc (M := S.mem) (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_
          janus_frame
        · janus_simp
        · janus_simp
        · janus_simp
        · refine (natVal_frame (m := S.mem) (rs := winA s K A) ?_ hzw').trans hv
          simp only [winA, K, A]; janus_frame
        · refine natNorm_frame (m := S.mem) (rs := winA s K A) ?_ hzw' hnorm
          simp only [winA, K, A]; janus_frame
        · refine (natVal_frame (m := S.mem) (rs := winA s K A) ?_ hywA).trans hyv
          simp only [winA, K, A]; janus_frame
        · janus_simp
        · janus_simp
        · rw [h18']; janus_simp
      all_goals try janus_simp
      · simp only [winA, K, A]; janus_frame
      · exact hya'


end FvModexp.Arm64.SubMod2N
