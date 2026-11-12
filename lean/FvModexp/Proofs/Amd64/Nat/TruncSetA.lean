import FvModexp.Proofs.Amd64.Nat.TruncSetC
import FvModexp.Proofs.Amd64.Nat.TruncMid

/-!
# `nat.trunc` (amd64): the `set` path (`len x < w`), allocation (`cap z < len x`): `makeslice(Word, 1, 1)`
(`len x = 1`) or `makeslice(Word, len x, len x + 4)` (`e - 56 = len x + 4`), reloads, to the join (`+0x1a2`), then
`copyS`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setAlloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibTrunc.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc n) (hw : xl < wOf n) (hz : zc < xl)
    (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hwa, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hsv, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, hn20,
    -, hcost, hinv⟩, hN, -⟩ := hpre'
  have hN' : NatNorm s.mem x xl := hN.resolve_right (by omega)
  have hk : xl = EvenHyp.truncNeed xl n := by unfold EvenHyp.truncNeed; unfold wOf at hw; omega
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
  by_cases hx1 : xl = 1
  · subst hx1
    have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by decide)
    rw [h_t] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost 1 = allocCost (8 * 1) by decide] at hcost; omega
    janus64_run [hsh, hsh', hwm, hzm, BitVec.msb_eq_decide] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := 1) (k := 1) hpre (Nat.le_refl _) hz hra hx15 hdf hF r1 r2
      (fun h => absurd h (by omega)) hcs hLF hMF hAp hIn (by omega)
      (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      h8 hinv' (by omega) (by omega) (by omega) (by decide)
    refine copyS impl R hmv b L zp zc x 1 n s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_) hw hN' _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
    all_goals (apply BitVec.eq_of_toNat_eq; simp)
  · have hx1' : (BitVec.ofNat 64 xl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply hx1
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl, xl + 4] := hsv.1 _ _ _ (by omega)
    rw [h_t] at hok1
    have hmc : makeCost xl = allocCost (8 * (xl + 4)) := by unfold makeCost makeCap; rw [if_neg hx1]
    have hbl := blockSize_le_allocCost (8 * (xl + 4)) true
    have hbs : blockSize (8 * (xl + 4)) true ≤ b := by omega
    have hx4 : (xl + 4) % 18446744073709551616 = xl + 4 := Nat.mod_eq_of_lt (by omega)
    have hx4' : BitVec.ofNat 64 xl + 4#64 = BitVec.ofNat 64 (xl + 4) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    janus64_run [hsh, hsh', hwm, hxm, hzm, hx1', hx4, hx4', BitVec.msb_eq_decide] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := xl + 4) (k := xl) hpre (Nat.le_refl _) hz hra hx15 hdf hF r1 r2
      (fun h => absurd h (by omega)) hcs hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by omega) (by omega) hrb (by omega)
    refine copyS impl R hmv b L zp zc x xl n s ptr.toNat (xl + 4) _ _ m (hmid ?hF ?_ ?_) hw hN' _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Amd64.Trunc
