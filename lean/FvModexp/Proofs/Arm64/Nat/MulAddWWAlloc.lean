import FvModexp.Proofs.Arm64.Nat.MulAddWWMid

/-!
# `nat.mulAddWW` (arm64): the entry → `makeslice(Word, m + 1, m + 5)` → `+0x7c` (`m ≠ 0`, `y ≠ 0`, `zc < m + 1`),
then `vww`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.MulAddWW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (h7 : s.regs 7 = r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hz : zc.toNat < xl.toNat + 1) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hx40, hz40, -, -, -, hxacc,
    hx48, hxh, hxw, hinv, hok⟩ := hpre'
  have hneed : need xl y r = xl.toNat + 1 := by unfold need; rw [if_neg (by omega)]
  rw [hneed] at hok
  obtain ⟨hok1, hcost⟩ := hok (by omega)
  rw [show makeCap (xl.toNat + 1) = xl.toNat + 5 by unfold makeCap; rw [if_neg (by omega)]] at hok1
  have hmc : makeCost (xl.toNat + 1) = allocCost (8 * (xl.toNat + 5)) := by
    unfold makeCost makeCap; rw [if_neg (by omega)]
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + 5)) true
  have hbs : blockSize (8 * (xl.toNat + 5)) true ≤ b := by omega
  have hwt : Apart wordT 16 (s.sp.toNat - 4208) (4208 + 72) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus_run [hx0', hy0'] until [hMid] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n (winA s 4208 72) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 72 ≤ a) → Outside a n
      [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8), (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  refine vww impl hap R b L zp zc xp xl xc y r s ptr.toNat (xl.toNat + 5) _ _ m
    (mid_of_alloc hpre hl4 hl48 ?hF ?_ ?_ ?_ ?_ hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
      hrb (by omega))
    hx0 hy0
    ((held_keep hxh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega))))
    _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [winA]; janus_frame
  all_goals try janus_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)

end FvModexp.Arm64.MulAddWW
