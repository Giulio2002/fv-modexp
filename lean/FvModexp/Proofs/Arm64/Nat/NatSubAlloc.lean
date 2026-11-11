import FvModexp.Proofs.Arm64.Nat.NatSubVV

/-!
# `nat.sub` (arm64): the entry → `makeslice(Word, m, makeCap m)` → `+0xd8` (`0 < n ≤ m`, `zc < m`), then `vv`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (LibNatSub.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = yp)
    (h7 : s.regs 7 = yl) (h8 : s.regs 8 = yc) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hz : zc.toNat < xl.toNat) (hpre : PreS 4304 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostR 4304 R b L zp zc xp xl yp yl s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, -, hge, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, hyacc, hy48, hyh, hyw, hinv, hok, -⟩ := hpre'
  obtain ⟨hok1, hcost⟩ := hok hz
  have hwt : Apart wordT 16 (s.sp.toNat - 4304) (4304 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n
      [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8), (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  by_cases h1 : xl.toNat = 1
  · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    subst hx1
    rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
    janus_run until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    refine vv impl hap R hmv b L zp zc xp 1#64 xc yp yl yc s ptr.toNat 1 _ _ m
      (mid_of_alloc hpre hyx hl4 hl48 hz ?hF ?_ ?_ ?_ ?_ ?_ ?_ hLF hMF hAp hIn (by omega)
        (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv'
        (by decide) (by decide) (by decide) (by decide))
      hyx hy0 hxc (by omega)
      ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega)))) hge
      _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1]] at hok1
    have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
      unfold makeCost makeCap; rw [if_neg h1]
    have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
    have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
    janus_run until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    refine vv impl hap R hmv b L zp zc xp xl xc yp yl yc s ptr.toNat (xl.toNat + 4) _ _ m
      (mid_of_alloc hpre hyx hl4 hl48 hz ?hF ?_ ?_ ?_ ?_ ?_ ?_ hLF hMF hAp hIn hle
        (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
        (by omega) (by omega) hrb (by omega))
      hyx hy0 hxc (by omega)
      ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega)))) hge
      _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

end FvModexp.Arm64.NatSub
