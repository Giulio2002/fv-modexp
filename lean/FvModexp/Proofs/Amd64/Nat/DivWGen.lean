import FvModexp.Proofs.Amd64.Nat.DivWMid
import FvModexp.Proofs.Amd64.Nat.DivWCall

/-!
# `nat.divW` (amd64): the entry → `+0xfb` on the `divWVW` path (`y ∉ {0, 1}`, `m > 0`): `z.make(m)` reusing `z`
(`zc ≥ m`) or allocating (`makeslice(Word, 1, 1)` for `m = 1`, `makeslice(Word, m, m + 4)` else), then `call`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem genReuse (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y) (hx0 : 0 < xl.toNat) (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1)
    (hz : xl.toNat ≤ zc.toNat) (hpre : Pre R b L zp zc xp xl y s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ Post R b L zp zc xp xl y s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, -, -, -, -⟩, -, -, hx40, hz40, -, hzw', -, hxacc, hx48, -, -, hxw, -, -, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hx0; simp at hx0
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  janus64_run [hx0', hy0', hy1', BitVec.msb_eq_decide] until [hMid]
  refine call impl hap R b L zp zc xp xl xc y s zp.toNat zc.toNat L b _
    (mid_of_reuse hpre hx0 hra hx15 hdf hz ?hF ?_ ?_).1 hy0 (mid_of_reuse hpre hx0 hra hx15 hdf hz ?hF ?_ ?_).2.1
    _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact hx15 | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem genAlloc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDivW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y) (hx0 : 0 < xl.toNat) (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1)
    (hz : zc.toNat < xl.toNat) (hpre : Pre R b L zp zc xp xl y s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ Post R b L zp zc xp xl y s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, -, hx40, hz40, -, -, -, hxacc, hx48, hxh, -,
    hxw, hinv, hok, -⟩ := hpre'
  obtain ⟨hok1, hcost⟩ := hok hz
  clear hok
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4232) (4232 + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  have hcs : ∀ r ∈ [((s.regs 4).toNat - 136 - 4096, (s.regs 4).toNat - 136),
      ((s.regs 4).toNat - 136 + 8, (s.regs 4).toNat - 136 + 8 + 24)],
      (s.regs 4).toNat - 4232 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 64 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  by_cases h1' : xl.toNat = 1
  · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1')
    subst hx1
    rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
    janus64_run [hy0', hy1', BitVec.msb_eq_decide] until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := 1) hpre hx0 hra hx15 hdf hF r1 r2 hcs hLF hMF hAp hIn
      (by omega) (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) h8 hinv'
      (by decide) (by decide) (by decide) (by decide)
    refine call impl hap R b L zp zc xp 1#64 xc y s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_).1 hy0 (hmid ?hF ?_ ?_).2.1
      _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | skip
  · have hx0'' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hx0; simp at hx0
    have hx1' : (xl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply h1'; rw [e]; rfl
    rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1']] at hok1
    have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
      unfold makeCost makeCap; rw [if_neg h1']
    have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
    have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
    janus64_run [hy0', hy1', hx0'', hx1', BitVec.msb_eq_decide, mod64_of_lt (a := xl.toNat + 4) (by omega)]
      until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := xl.toNat + 4) hpre hx0 hra hx15 hdf hF r1 r2 hcs hLF hMF hAp
      hIn hle (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by omega) (by omega) hrb (by omega)
    refine call impl hap R b L zp zc xp xl xc y s ptr.toNat (xl.toNat + 4) _ _ m (hmid ?hF ?_ ?_).1 hy0
      (hmid ?hF ?_ ?_).2.1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | skip

end FvModexp.Amd64.DivW
