import FvModexp.Proofs.Amd64.Nat.MulAddWWMid
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.mulAddWW` (amd64): the entry → `makeslice(Word, m + 1, m + 5)` → `+0xae` (`m ≠ 0`, `y ≠ 0`, `zc < m + 1`),
then `vww`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (held_keep)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.MulAddWW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y r) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hz : zc.toNat < xl.toNat + 1) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, hx40, hz40, -, -, -, hxacc, hx48, hxh, hxw,
    hinv, hok⟩ := hpre'
  have hneed : need xl y r = xl.toNat + 1 := by unfold need; rw [if_neg (by omega)]
  rw [hneed] at hok
  obtain ⟨hok1, hcost⟩ := hok (by omega)
  rw [show makeCap (xl.toNat + 1) = xl.toNat + 5 by unfold makeCap; rw [if_neg (by omega)]] at hok1
  have hmc : makeCost (xl.toNat + 1) = allocCost (8 * (xl.toNat + 5)) := by
    unfold makeCost makeCap; rw [if_neg (by omega)]
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + 5)) true
  have hbs : blockSize (8 * (xl.toNat + 5)) true ≤ b := by omega
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4208) (4208 + 72) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  janus64_run [hx0', hy0', BitVec.msb_eq_decide, mod64_of_lt (a := xl.toNat + 1) (by omega),
    mod64_of_lt (a := xl.toNat + 5) (by omega),
    toInt_small (xl + 1#64) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] until [hMid] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n (win s 4208 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 72 ≤ a) → Outside a n
      [((s.regs 4).toNat - 112 - 4096, (s.regs 4).toNat - 112),
        ((s.regs 4).toNat - 112 + 8, (s.regs 4).toNat - 112 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  refine vww impl hap R b L zp zc xp xl xc y r s ptr.toNat (xl.toNat + 5) _ _ m
    (mid_of_alloc hpre hra hx15 hdf ?hF ?_ ?_ ?_ ?_ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega) hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega)))
      hinv' hrb (by omega))
    hx0 hy0
    ((held_keep hxh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega))))
    _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)

end FvModexp.Amd64.MulAddWW
