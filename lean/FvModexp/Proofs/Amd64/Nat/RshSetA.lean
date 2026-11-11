import FvModexp.Proofs.Amd64.Nat.RshSet
import FvModexp.Proofs.Amd64.Nat.RshMid

/-!
# `nat.rsh` (amd64): `s = 0`, `cap z = 0`: entry → `z.make(len x)` (`makeslice(Word, m, m + 4)` at `+0xd5`, or
`makeslice(Word, 1, 1)` at `+0xa0` for `m = 1`) → `+0xf2`, then `copyS`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setAlloc (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibRsh.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc 0) (hzc : zc = 0) (hpre : Pre R b L zp zl zc x xl 0 s) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl 0 s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hsv, hzl, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, -,
    hN, hxl0, -, hcost, hinv⟩ := hpre'
  subst hzc
  have hzl0 : zl = 0 := by omega
  subst hzl0
  have hn0 : 0 < need xl 0 := by simp only [need]; omega
  have hz : 0 < need xl 0 := hn0
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4248) (4248 + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  have hx0 := ofNat_ne0 xl hxl0 (by omega)
  have hxm : xl % 2 ^ 64 = xl := Nat.mod_eq_of_lt (by omega)
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  have hcs : ∀ r ∈ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
      ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)],
      (s.regs 4).toNat - 4248 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 56 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  simp only [LiveSep, win] at hLs
  by_cases h1x : xl = 1
  · subst h1x
    have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by omega)
    have hmcost : makeCost (need 1 0) = allocCost (8 * 1) := by decide
    rw [hmcost] at hcost
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by omega
    rw [h_t] at hty hok1 hwt
    janus64_run [hx0, hxm, BitVec.msb_eq_decide] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (round := _) hpre hz hra hx15 hdf hF r1 r2 hn0 hcs hLF
      hMF hAp hIn (by omega) (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      h8 hinv' (c := 1) (by decide) (by decide) (by omega) (by rw [hmcost]; decide)
    refine copyS impl R hmv b L zp 0 x 1 s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_) hN _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
  · have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl, xl + 4] := hsv.1 _ _ _ (by omega)
    have hmcost : makeCost (need xl 0) = allocCost (8 * (xl + 4)) := by
      unfold makeCost makeCap; simp only [need, Nat.zero_div, Nat.sub_zero]; rw [if_neg h1x]
    rw [hmcost] at hcost
    have hbl := blockSize_le_allocCost (8 * (xl + 4)) true
    have hbs : blockSize (8 * (xl + 4)) true ≤ b := by omega
    rw [h_t] at hty hok1 hwt
    have hx1 : (BitVec.ofNat 64 xl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have hn4 := add_c xl 4 (by omega)
    have hm4 : (xl + 4) % 2 ^ 64 = xl + 4 := Nat.mod_eq_of_lt (by omega)
    janus64_run [hx0, hxm, hx1, hn4, hm4, BitVec.msb_eq_decide] until [hJoinS] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (round := _) hpre hz hra hx15 hdf hF r1 r2 hn0 hcs hLF
      hMF hAp hIn hle (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (c := xl + 4) (by simp only [need]; omega) (by omega) hrb (by rw [hmcost]; omega)
    refine copyS impl R hmv b L zp 0 x xl s ptr.toNat (xl + 4) _ _ m (hmid ?hF ?_ ?_) hN _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Amd64.Rsh
