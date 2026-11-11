import FvModexp.Proofs.Amd64.Nat.DivWSet

/-!
# `nat.divW` (amd64): the entry → `+0x1b2` on the `z.set(x)` path (`y = 1`, `m > 0`), then `setTail`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem setPath (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDivW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc 1#64) (hx0 : 0 < xl.toNat) (hpre : Pre R b L zp zc xp xl 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ Post R b L zp zc xp xl 1#64 s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, -, hx40, hz40, -, -, -, hxacc, hx48, hxh, -,
    hxw, hinv, hok, -⟩ := hpre'
  by_cases hz : xl.toNat ≤ zc.toNat
  · clear hok
    janus64_run [BitVec.msb_eq_decide] until [hSet]
    refine setTail impl R hmv b L zp zc xp xl s zp.toNat zc.toNat L b _
      (mid_of_reuse hpre hx0 hra hx15 hdf hz ?hF ?_ ?_).1 (mid_of_reuse hpre hx0 hra hx15 hdf hz ?hF ?_ ?_).2.1
      (mid_of_reuse hpre hx0 hra hx15 hdf hz ?hF ?_ ?_).2.2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | skip
  · obtain ⟨hok1, hcost⟩ := hok (by omega)
    clear hok
    have hwt : Apart wordT 16 ((s.regs 4).toNat - 4232) (4232 + 64) := apart_of_data hd 1 (by decide) (by decide) hw
    unfold Apart at hwt hga
    janus64_data hd
    janus_eval_nat h_t : wordT
    rw [h_t] at hty hok1 hwt
    simp only [LiveSep, win] at hLs
    simp only [win, outside_cons, outside_nil, and_true] at hxw
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
      janus64_run [BitVec.msb_eq_decide] until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
      have hmid := fun hF r1 r2 => mid_of_alloc (c := 1) hpre hx0 hra hx15 hdf hF r1 r2 hcs hLF hMF hAp hIn
        (by omega) (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) h8 hinv'
        (by decide) (by decide) (by decide) (by decide)
      refine setTail impl R hmv b L zp zc xp 1#64 s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_).1 (hmid ?hF ?_ ?_).2.1
        (hmid ?hF ?_ ?_).2.2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [win]; janus_frame
      all_goals try janus64_simp
      all_goals first | exact hx15 | skip
    · have hx1' : (xl = 1#64) = False := by
        simp only [eq_iff_iff, iff_false]; intro e; apply h1'; rw [e]; rfl
      rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1']] at hok1
      have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
        unfold makeCost makeCap; rw [if_neg h1']
      have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
      have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
      janus64_run [hx1', BitVec.msb_eq_decide, mod64_of_lt (a := xl.toNat + 4) (by omega)] until [hSet]
        calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
      have hmid := fun hF r1 r2 => mid_of_alloc (c := xl.toNat + 4) hpre hx0 hra hx15 hdf hF r1 r2 hcs hLF hMF hAp
        hIn hle (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
        (h8 (Or.inr (by omega))) hinv' (by omega) (by omega) hrb (by omega)
      refine setTail impl R hmv b L zp zc xp xl s ptr.toNat (xl.toNat + 4) _ _ m (hmid ?hF ?_ ?_).1
        (hmid ?hF ?_ ?_).2.1 (hmid ?hF ?_ ?_).2.2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [win]; janus_frame
      all_goals try janus64_simp
      all_goals first | exact hx15 | skip

end FvModexp.Amd64.DivW
