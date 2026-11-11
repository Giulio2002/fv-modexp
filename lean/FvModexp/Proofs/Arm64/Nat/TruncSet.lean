import FvModexp.Proofs.Arm64.Nat.TruncSetC
import FvModexp.Proofs.Arm64.Nat.TruncMid
import FvModexp.Proofs.Arm64.Nat.TruncMain

/-!
# `nat.trunc` (arm64): the `set` path (`len x < w`) from the entry to the join of `z.make(len x)` (`+0x170`), then
`copyS`: reuse (`len x ≤ cap z`), `makeslice(Word, 1, 1)`, `makeslice(Word, len x, len x + 4)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Trunc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setReuse (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 n)
    (hw : xl < wOf n) (hz : xl ≤ zc) (hz0 : 0 < zc) (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh2 : (BitVec.ofNat 64 n + 63#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (wOf n) := by rw [TruncMath.rot6, hsh]
  have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
  janus_run [hsh, hsh2, hwm] until [hJoinS]
  refine copyS impl R hmv b L zp zc x xl n s zp zc L b _
    (mid_of_reuse hpre (Nat.le_refl _) hz hz0 hl4 hl48 ?hF ?_ ?_ (fun h => absurd h (by omega))) hw hpre.2.1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals janus_simp
  all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setAlloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibTrunc.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 n)
    (hw : xl < wOf n) (hz : zc < xl) (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, hn20, -, hcost, hinv⟩, -, -⟩ := hpre'
  have hk : xl = EvenHyp.truncNeed xl n := by unfold EvenHyp.truncNeed; unfold wOf at hw; omega
  rw [← hk] at hcost
  have hsh := shr_w n hn20
  have hsh2 : (BitVec.ofNat 64 n + 63#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (wOf n) := by rw [TruncMath.rot6, hsh]
  have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 4208) (4208 + 64) := apart_of_data hd 1 (by decide) (by decide) hwa
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl, makeCap xl] :=
    hsv.1 _ _ _ (by unfold makeCap; split <;> omega)
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4208 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  by_cases hw1 : xl = 1
  · subst hw1
    rw [show makeCap 1 = 1 by decide] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost 1 = allocCost (8 * 1) by decide] at hcost; omega
    janus_run [hsh, hsh2, hwm] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 rn => mid_of_alloc (c := 1) (k := 1) hpre (Nat.le_refl _) hz hl4 hl48 hF r1 r2 rn hLF hMF hAp
      hIn (by omega) (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
      (by omega) (by omega) (by omega) (by decide)
    refine copyS impl R hmv b L zp zc x 1 n s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_ (fun h => absurd h (by omega))) hw hpre.2.1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp)
  · have hw1' : (BitVec.ofNat 64 xl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply hw1
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    rw [show makeCap xl = xl + 4 by unfold makeCap; rw [if_neg hw1]] at hok1
    have hmc : makeCost xl = allocCost (8 * (xl + 4)) := by unfold makeCost makeCap; rw [if_neg hw1]
    have hbl := blockSize_le_allocCost (8 * (xl + 4)) true
    have hbs : blockSize (8 * (xl + 4)) true ≤ b := by omega
    janus_run [hsh, hsh2, hwm, hw1'] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 rn => mid_of_alloc (c := xl + 4) (k := xl) hpre (Nat.le_refl _) hz hl4 hl48 hF r1 r2 rn hLF
      hMF hAp hIn hle (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by omega) (by omega) hrb (by omega)
    refine copyS impl R hmv b L zp zc x xl n s ptr.toNat (xl + 4) _ _ m (hmid ?hF ?_ ?_ (fun h => absurd h (by omega))) hw hpre.2.1 _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Arm64.Trunc
