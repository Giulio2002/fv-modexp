import FvModexp.Proofs.Amd64.Nat.TruncCopy
import FvModexp.Proofs.Amd64.Nat.TruncMid

/-!
# `nat.trunc` (amd64): the main path (`w ≤ len x`), allocation (`cap z < w`): `makeslice(Word, 1, 1)` (`w = 1`) or
`makeslice(Word, w, w + 4)` (`e - 32 = w`, `e - 64 = w + 4`), reloads, to the join (`+0xbb`), then `copyM`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainAlloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibTrunc.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc n) (hw : wOf n ≤ xl) (hz : zc < wOf n)
    (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hwa, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hsv, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, hn20,
    -, hcost, hinv⟩, -, -⟩ := hpre'
  have hk : wOf n = EvenHyp.truncNeed xl n := by unfold EvenHyp.truncNeed; unfold wOf at hw ⊢; omega
  rw [← hk] at hcost
  have hsh := shr_w n hn20
  have hsh' := shr_w' n hn20
  have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
  have hxm : xl % 18446744073709551616 = xl := Nat.mod_eq_of_lt (by omega)
  have hzm : zc % 18446744073709551616 = zc := Nat.mod_eq_of_lt (by omega)
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4192) (4192 + 64) := apart_of_data hd 1 (by decide) (by decide) hwa
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hwt
  simp only [LiveSep, win] at hLs
  have hcs : ∀ r ∈ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96),
      ((s.regs 4).toNat - 96 + 8, (s.regs 4).toNat - 96 + 8 + 24)],
      (s.regs 4).toNat - 4192 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 64 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  by_cases hw1 : wOf n = 1
  · have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by decide)
    rw [h_t] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost (wOf n) = allocCost (8 * 1) by rw [hw1]; decide] at hcost; omega
    have hw1' : BitVec.ofNat 64 (wOf n) = 1#64 := by rw [hw1]
    rw [hw1'] at hsh hsh'
    janus64_run [hsh, hsh', hxm, hzm, BitVec.msb_eq_decide] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 rn => mid_of_alloc (c := 1) (k := wOf n) hpre hw hz hra hx15 hdf hF r1 r2 rn hcs hLF
      hMF hAp hIn (by omega) (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      h8 hinv' (by omega) (by omega) (by omega) (by rw [hw1]; decide)
    refine copyM impl R hmv b L zp zc x xl n s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_ (fun _ => ?_)) hk hn20 _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | (rw [hw1]) | skip
    all_goals (apply BitVec.eq_of_toNat_eq; simp)
  · have hw1' : (BitVec.ofNat 64 (wOf n) = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply hw1
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; unfold wOf at this ⊢; omega
    have hok1 : R.ok (cA "runtime.makeslice") [wordT, wOf n, wOf n + 4] := hsv.1 _ _ _ (by unfold wOf; omega)
    rw [h_t] at hok1
    have hmc : makeCost (wOf n) = allocCost (8 * (wOf n + 4)) := by unfold makeCost makeCap; rw [if_neg hw1]
    have hbl := blockSize_le_allocCost (8 * (wOf n + 4)) true
    have hbs : blockSize (8 * (wOf n + 4)) true ≤ b := by omega
    have hw4 : (wOf n + 4) % 18446744073709551616 = wOf n + 4 := Nat.mod_eq_of_lt (by unfold wOf; omega)
    have hw4' : BitVec.ofNat 64 (wOf n) + 4#64 = BitVec.ofNat 64 (wOf n + 4) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold wOf; omega
    janus64_run [hsh, hsh', hwm, hxm, hzm, hw1', hw4, hw4', BitVec.msb_eq_decide] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 rn => mid_of_alloc (c := wOf n + 4) (k := wOf n) hpre hw hz hra hx15 hdf hF r1 r2 rn
      hcs hLF hMF hAp hIn hle (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by omega) (by omega) hrb (by omega)
    refine copyM impl R hmv b L zp zc x xl n s ptr.toNat (wOf n + 4) _ _ m (hmid ?hF ?_ ?_ (fun _ => ?_)) hk hn20 _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Amd64.Trunc
