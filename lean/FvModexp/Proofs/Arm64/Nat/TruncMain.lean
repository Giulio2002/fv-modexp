import FvModexp.Proofs.Arm64.Nat.TruncCopy
import FvModexp.Proofs.Arm64.Nat.TruncMid

/-!
# `nat.trunc` (arm64): the main path (`w ≤ len x`) from the entry to the join of `z.make(w)` (`+0xa0`), then `copyM`

`z.make(w)`: reuse (`w ≤ cap z`, `BGE`), `makeslice(Word, 1, 1)` (`w = 1`), `makeslice(Word, w, w + 4)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Trunc

theorem shr_w (n : Nat) (hn : n ≤ 2 ^ 20) : (BitVec.ofNat 64 n + 63#64) >>> 6 = BitVec.ofNat 64 (wOf n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  unfold wOf; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainReuse (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 n)
    (hw : wOf n ≤ xl) (hz : wOf n ≤ zc) (hz0 : 0 < zc) (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh2 : (BitVec.ofNat 64 n + 63#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (wOf n) := by rw [TruncMath.rot6, hsh]
  janus_run [hsh, hsh2] until [hJoin]
  refine copyM impl R hmv b L zp zc x xl n s zp zc L b _
    (mid_of_reuse hpre hw hz hz0 hl4 hl48 ?hF ?_ ?_ (fun _ => ?_)) hw _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (by unfold EvenHyp.truncNeed; unfold wOf at hw ⊢; omega) hn20
  case hF => simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainAlloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibTrunc.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 n)
    (hw : wOf n ≤ xl) (hz : zc < wOf n) (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, hn20, -, hcost, hinv⟩, -, -⟩ := hpre'
  have hk : wOf n = EvenHyp.truncNeed xl n := by unfold EvenHyp.truncNeed; unfold wOf at hw ⊢; omega
  rw [← hk] at hcost
  have hsh := shr_w n hn20
  have hsh2 : (BitVec.ofNat 64 n + 63#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (wOf n) := by rw [TruncMath.rot6, hsh]
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 4208) (4208 + 64) := apart_of_data hd 1 (by decide) (by decide) hwa
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, wOf n, makeCap (wOf n)] :=
    hsv.1 _ _ _ (by unfold makeCap; split <;> omega)
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4208 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  by_cases hw1 : wOf n = 1
  · rw [show makeCap (wOf n) = 1 by rw [hw1]; decide, hw1] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost (wOf n) = allocCost (8 * 1) by rw [hw1]; decide] at hcost; omega
    have hsh3 : BitVec.ofNat 64 (wOf n) = 1#64 := by rw [hw1]
    rw [hsh3] at hsh hsh2
    janus_run [hsh, hsh2] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 rn => mid_of_alloc (c := 1) (k := wOf n) hpre hw hz hl4 hl48 hF r1 r2 rn hLF hMF hAp
      hIn (by omega) (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
      (by omega) (by omega) (by omega) (by rw [hw1]; decide)
    refine copyM impl R hmv b L zp zc x xl n s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_ (fun _ => ?_)) hw _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ rfl hk hn20
    case hF => simp only [winA]; janus_frame
    all_goals first | janus_simp | (rw [hw1]; janus_simp)
    all_goals first | omega | (rw [hw1]) | (apply BitVec.eq_of_toNat_eq; simp)
  · have hw1' : (BitVec.ofNat 64 (wOf n) = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply hw1
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; unfold wOf at this ⊢; omega
    rw [show makeCap (wOf n) = wOf n + 4 by unfold makeCap; rw [if_neg hw1]] at hok1
    have hmc : makeCost (wOf n) = allocCost (8 * (wOf n + 4)) := by unfold makeCost makeCap; rw [if_neg hw1]
    have hbl := blockSize_le_allocCost (8 * (wOf n + 4)) true
    have hbs : blockSize (8 * (wOf n + 4)) true ≤ b := by omega
    janus_run [hsh, hsh2, hw1'] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 rn => mid_of_alloc (c := wOf n + 4) (k := wOf n) hpre hw hz hl4 hl48 hF r1 r2 rn hLF
      hMF hAp hIn hle (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by omega) (by omega) hrb (by omega)
    refine copyM impl R hmv b L zp zc x xl n s ptr.toNat (wOf n + 4) _ _ m (hmid ?hF ?_ ?_ (fun _ => ?_)) hw _ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ rfl hk hn20
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Arm64.Trunc
