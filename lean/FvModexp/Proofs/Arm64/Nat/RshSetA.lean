import FvModexp.Proofs.Arm64.Nat.RshSet

/-! # `nat.rsh` (arm64): `s = 0`, `cap z = 0`: entry to the join of `z.make(len x)` (`makeslice`), then `copyS` -/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setAlloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibRsh.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 0)
    (hzc : zc = 0) (hpre : Pre R b L zp zl zc x xl 0 s) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl 0 s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, -, -, -, -, hcost, hinv⟩ := hpre'
  have hxl0 : 0 < xl := hpre.2.2.2.2.2.2.2.2.1
  subst hzc
  have hn0 : 0 < need xl 0 := by simp only [need]; omega
  have hz : 0 < need xl 0 := hn0
  have hzl : zl = 0 := by omega
  subst hzl
  have hx0 : (BitVec.ofNat 64 xl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hne : (BitVec.ofNat 64 0 = BitVec.ofNat 64 xl) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 4240) (4240 + 64) := apart_of_data hd 1 (by decide) (by decide) hwa
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hwt
  simp only [LiveSep, win] at hLs
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  by_cases hk1 : xl = 1
  · have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by omega)
    rw [h_t] at hok1
    have hmc : makeCost (need xl 0) = allocCost (8 * 1) := by
      simp only [need]; rw [hk1]; decide
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by omega
    have hn1 : BitVec.ofNat 64 xl = 1#64 := by rw [hk1]
    janus_run [hn1, hx0, hne] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := 1) hpre hz hn0 (by simp only [need]; omega)
      (by simp only [need]; omega) hl4 hl48 hF r1 r2 hLF hMF hAp hIn (by omega)
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv' (by omega)
      (by rw [hmc]; exact Nat.le_trans (by decide) hbl)
    refine copyS impl R hmv b L zp 0 x xl s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_) hpre.2.2.2.2.2.2.2.1 _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals try janus_simp
    all_goals try (simp only [need]; omega)
    all_goals try omega
    all_goals try (apply BitVec.eq_of_toNat_eq; simp)
    all_goals omega
  · have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl, xl + 4] := hsv.1 _ _ _ (by omega)
    rw [h_t] at hok1
    have hmc : makeCost (need xl 0) = allocCost (8 * (xl + 4)) := by
      unfold makeCost makeCap; simp only [need, Nat.zero_div, Nat.sub_zero]; rw [if_neg hk1]
    have hbl := blockSize_le_allocCost (8 * (xl + 4)) true
    have hbs : blockSize (8 * (xl + 4)) true ≤ b := by omega
    have hk1' : (BitVec.ofNat 64 xl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have h4' : BitVec.ofNat 64 xl + 4#64 = BitVec.ofNat 64 (xl + 4) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    janus_run [hx0, hne, hk1', h4'] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := xl + 4) hpre hz hn0 (by simp only [need]; omega)
      (by simp only [need]; omega) hl4 hl48 hF r1 r2 hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
      hrb (by rw [hmc]; omega)
    refine copyS impl R hmv b L zp 0 x xl s ptr.toNat (xl + 4) _ _ m (hmid ?hF ?_ ?_)
      hpre.2.2.2.2.2.2.2.1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Arm64.Rsh
