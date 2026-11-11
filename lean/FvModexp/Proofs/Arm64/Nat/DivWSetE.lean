import FvModexp.Proofs.Arm64.Nat.DivWSet

/-!
# `nat.divW` (arm64): the entry → `+0x174` on the `z.set(x)` path (`y = 1`, `m > 0`): `z.make(m)` reusing `z`
(`zc ≥ m`) or allocating (`makeslice(Word, 1, 1)` for `m = 1`, `makeslice(Word, m, m + 4)` else), then `setTail`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivW

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setPath (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDivW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = 1#64)
    (hx0 : 0 < xl.toNat) (hpre : Pre R b L zp zc xp xl 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl 1#64 s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, -, hx40, hz40, -, -, -, hxacc,
    hx48, hxh, -, hxw, hinv, hok, -⟩ := hpre'
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  by_cases hz : xl.toNat ≤ zc.toNat
  · clear hok
    janus_run until [hSet]
    refine setTail impl R hmv b L zp zc xp xl s zp.toNat zc.toNat L b _
      (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).1 (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).2.1
      (mid_of_reuse hpre hx0 hl4 hl48 hz ?hF ?_ ?_).2.2 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · obtain ⟨hok1, hcost⟩ := hok (by omega)
    clear hok
    have hwt : Apart wordT 16 (s.sp.toNat - 4240) (4240 + 64) := apart_of_data hd 1 (by decide) (by decide) hw
    unfold Apart at hwt hga
    janus_data hd
    janus_eval_nat h_t : wordT
    rw [h_t] at hty hok1 hwt
    simp only [LiveSep, win] at hLs
    simp only [win, outside_cons, outside_nil, and_true] at hxw
    by_cases h1 : xl.toNat = 1
    · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
      subst hx1
      rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
      have hbl := blockSize_le_allocCost (8 * 1) true
      have hbs : blockSize (8 * 1) true ≤ b := by
        rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
      janus_run until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
      have hmid := fun hF r1 r2 => mid_of_alloc (c := 1) hpre hx0 hl4 hl48 hF r1 r2 hLF hMF hAp hIn (by omega)
        (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
        (by decide) (by decide) (by decide) (by decide)
      refine setTail impl R hmv b L zp zc xp 1#64 s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_).1 (hmid ?hF ?_ ?_).2.1
        (hmid ?hF ?_ ?_).2.2 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [winA]; janus_frame
      all_goals janus_simp
    · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1]] at hok1
      have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
        unfold makeCost makeCap; rw [if_neg h1]
      have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
      have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
      janus_run until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
      have hmid := fun hF r1 r2 => mid_of_alloc (c := xl.toNat + 4) hpre hx0 hl4 hl48 hF r1 r2 hLF hMF hAp hIn hle
        (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
        (by omega) (by omega) hrb (by omega)
      refine setTail impl R hmv b L zp zc xp xl s ptr.toNat (xl.toNat + 4) _ _ m (hmid ?hF ?_ ?_).1
        (hmid ?hF ?_ ?_).2.1 (hmid ?hF ?_ ?_).2.2 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [winA]; janus_frame
      all_goals janus_simp

end FvModexp.Arm64.DivW
