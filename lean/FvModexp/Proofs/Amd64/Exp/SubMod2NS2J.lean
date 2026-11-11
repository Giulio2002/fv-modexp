import FvModexp.Proofs.Amd64.Exp.SubMod2NCall

/-!
# `nat.subMod2N` (amd64): the two ways into `J2` (agent infra)

`j2_skip` (no truncation of `y`) and `s2t` (after `y = nat(nil).trunc(y, n)` returns).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
/-- `J2` reached with `y' = y` (no truncation: `Y < 2^n`) after the stores of the `x'` locals -/
theorem j2_skip {impl : List Amd64.Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {op zp zl zc yp yl yc n : Nat}
    {s : State} (k2 : J2 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    {M : Memory} {l1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : Rt R b L s zp zc n 1 M L1 b1)
    (hv : natVal M zp l1 = natVal s.mem zp zl % 2 ^ n) (hnorm : NatNorm M zp l1) (hlc : l1 ≤ zc)
    (S : State) (hF : MemFrame M S.mem (win s K A)) (hreg : S.mem.regions = M.regions)
    (hpc : S.rip = BitVec.ofNat 64 6216422) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128))
    (hab : Abi s S)
    (h7 : S.regs 7 = BitVec.ofNat 64 zp) (h6 : S.regs 6 = BitVec.ofNat 64 l1) (h8 : S.regs 8 = BitVec.ofNat 64 zc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hfw : Fw s S.mem zp zl zc yp n) (r16 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = zp)
    (r40 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = l1) (r32 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = zc)
    (hyv : natVal s.mem yp yl < 2 ^ n) :
    Goal impl R b L zp zl zc yp yl n s S := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨-, -, hw⟩, -, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, hyl, hyc, -, -, hzw, -, -, hya,
    hy48, hyh, hyw, hyn, hzy, -⟩ := hpre'
  have hrt' := rt_mono (rt_stk hpre (hrt) hF hreg) (show 1 ≤ 2 by omega)
  have hzw' : Outside zp (8 * l1) (win s K A) := by
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw ⊢; omega
  have hzyl : Apart yp (8 * yl) zp (8 * zc) := by unfold Apart at hzy ⊢; omega
  have hvy : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hrt' hyh hyw hzyl
  have hyn' : NatNorm S.mem yp yl := by
    rcases hyn with h | h
    · exact Or.inl h
    rcases Nat.eq_zero_or_pos yl with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    rw [rd_held hrt' (hyh.sub (by omega) (by omega)) (hyw.of_sub (by omega) (by omega))
      (by unfold Apart at hzyl ⊢; omega)]
    exact h
  have hxl := len_le_W hnorm (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  refine k2 S _ yp yl yc L1 b1 hpre hpc hsp hab h7 h6 h8 h9 h10 h11 hfw r16 r40 r32 hrt' ?_ ?_ hxl ?_ ?_ ?_ hyl
    (by omega) ?_ hy48 (hrt.2.2.2.1.held hyh) ?_ (by unfold Apart at hzy ⊢; omega)
  · rw [natVal_frame hF hzw', hv]
  · exact natNorm_frame hF hzw' hnorm
  · rw [hvy, Nat.mod_eq_of_lt hyv]
  · exact hyn'
  · exact len_le_W hyn' (by rw [hvy]; exact hyv)
  · rw [hF.accessible, hrt.2.1.accessible]; exact hya
  · simp only [win, K, A, outside_cons, outside_nil, and_true] at hyw; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- after `y = nat(nil).trunc(y, n)` returns (at `+0x22e`): reload `x'`, move the result to `R9..R11`, `J2` -/
theorem s2t (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k2 : J2 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (M0 : Memory) {l1 : Nat} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt0 : Rt R b L s zp zc n 1 M0 L1 b1)
    (hfw0 : Fw s M0 zp zl zc yp n) (r16 : M0.readLE ((s.regs 4).toNat - 16) 8 = zp)
    (r40 : M0.readLE ((s.regs 4).toNat - 40) 8 = l1) (r32 : M0.readLE ((s.regs 4).toNat - 32) 8 = zc)
    (hv0 : natVal M0 zp l1 = natVal s.mem zp zl % 2 ^ n) (hn0 : NatNorm M0 zp l1) (hlc : l1 ≤ zc) (hy1 : 1 ≤ yl)
    (hyv0 : natVal M0 yp yl = natVal s.mem yp yl)
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 136)
    (h140 : S0.regs 14 = s.regs 14) (hfs0 : S0.fsBase = s.fsBase) (hx0 : S0.xmm 15 = s.xmm 15)
    (hdf0 : S0.df = false)
    (s' : State) (hpc' : s'.rip = BitVec.ofNat 64 6216398) (hsp' : s'.regs 4 = S0.regs 4 + 8)
    (h14' : s'.regs 14 = S0.regs 14) (hx' : s'.xmm 15 = S0.xmm 15) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b1 L1 stkT aboveT 0 0 yp yl n S0 s') :
    Goal impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, -, -, hzl, hW, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  simp only [W] at hW
  obtain ⟨hfs, hdf, p', l', c', e0, e1, e2, L', b', ⟨hv, hnorm, hlc', hc40, hlive, -, hfresh⟩, hcap, ⟨hLE, hbud, hinv⟩,
    hF, hLF⟩ := hpost
  have hneed : 0 < truncNeed yl n := by unfold truncNeed; have := hpre.2.2.2.2.2.2.1; omega
  have hc1 : truncNeed yl n ≤ c' := hcap hneed
  obtain ⟨hIn, hAp⟩ := hfresh hneed (by omega)
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hlive (by omega)
  simp only [win, hsp0] at hF
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hacc' : s'.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hF.accessible, hS0, hrt0.2.1.accessible]; exact hw
  have rd : ∀ a, (s.regs 4).toNat - 56 ≤ a → a + 8 ≤ (s.regs 4).toNat + 88 → s'.mem.readLE a 8 = M0.readLE a 8 := by
    intro a h1 h2
    rw [← hS0]
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw0
  have q16 := (rd _ (by omega) (by omega)).trans r16
  have q40 := (rd _ (by omega) (by omega)).trans r40
  have q32 := (rd _ (by omega) (by omega)).trans r32
  have hsp'' : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) := by
    rw [hsp']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp0]; omega
  have hzh : Held R L1 zp (8 * zc) := (hrt0.2.2.2.2.2.2 (by omega)).2.1
  have hzh1 : Held R L1 zp (8 * l1) := hzh.sub (Nat.le_refl _) (by omega)
  have hrt1 : Rt R b L s zp zc n 2 s'.mem L' b' := by
    rw [hS0] at hF hreg' hLF
    rw [h140] at hinv
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
  have a16 : (s.regs 4).toNat - 128 + 112 = (s.regs 4).toNat - 16 := by omega
  have a40 : (s.regs 4).toNat - 128 + 88 = (s.regs 4).toNat - 40 := by omega
  have a32 : (s.regs 4).toNat - 128 + 96 = (s.regs 4).toNat - 32 := by omega
  unfold Goal
  janus64_run [hsp'', a16, a40, a32, q16, q40, q32] until [6216422]
  refine k2 _ l1 p' l' c' L' b' hpre ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrt1 ?_ ?_ ?_ ?_ ?_ ?_ hlc'
    hc40 ?_ ?_ ?_ ?_ ?_
  all_goals try janus64_simp
  all_goals first
    | exact hsp'.symm.trans hsp'' | (rw [h14', h140]) | (rw [hfs, hfs0]) | (rw [hx', hx0]) | (rw [hdf, hdf0])
    | exact ⟨(rd _ (by omega) (by omega)).trans f1, (rd _ (by omega) (by omega)).trans f2,
        (rd _ (by omega) (by omega)).trans f3, (rd _ (by omega) (by omega)).trans f4,
        (rd _ (by omega) (by omega)).trans f5, (rd _ (by omega) (by omega)).trans f6,
        (rd _ (by omega) (by omega)).trans f7⟩
    | exact q16 | exact q40 | exact q32
    | (rw [hzx]; exact hv0) | exact hzn
    | exact len_le_W hn0 (by rw [hv0]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
    | (rw [hv, hS0, hyv0]) | exact hnorm
    | exact len_le_W hnorm (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
    | (rw [← hS0, ← hF.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (Nat.le_refl _) (by omega))
    | omega
    | exact hph.sub (Nat.le_refl _) (by omega)
    | (have := apart_fresh hzh hAp hIn; unfold Apart at this ⊢; omega)

end FvModexp.Amd64.SubMod2N
