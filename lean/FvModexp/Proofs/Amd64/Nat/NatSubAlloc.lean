import FvModexp.Proofs.Amd64.Nat.NatSubReuse

/-! # `nat.sub` (amd64): the entry → `makeslice(Word, m, makeCap m)` → `+0x13d` (`0 < n ≤ m`, `zc < m`), then `vv` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibNatSub.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hz : zc.toNat < xl.toNat) (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostS 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, -, hge, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, hyacc, hy48, hyh, hyw, hinv, hok, -⟩ := hpre'
  obtain ⟨hok1, hcost⟩ := hok hz
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4288) (4288 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n
      [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  by_cases h1x : xl.toNat = 1
  · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1x)
    subst hx1
    rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by
      rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
    janus64_run [BitVec.msb_eq_decide] until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    refine vv impl hap R hmv b L zp zc xp 1#64 xc yp yl yc s ptr.toNat 1 _ _ m
      (mid_of_alloc hpre hyx hra hx15 hdf ?hF ?_ ?_ ?_ ?_ ?_ ?_ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp only <;> omega) hLF hMF hAp hIn (by omega)
        (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) h8
        hinv' (by decide) (by decide) (by decide) (by decide))
      hyx hy0 hxc (by omega)
      ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hF (hWo _ _ (by omega))))
      ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega)))) hge
      _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals janus64_simp


  · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1x]] at hok1
    have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
      unfold makeCost makeCap; rw [if_neg h1x]
    have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
    have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
    janus64_run [BitVec.msb_eq_decide, FvModexp.mod64_of_lt (xl.toNat + 4) (by omega)] until [hMid] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
    refine vv impl hap R hmv b L zp zc xp xl xc yp yl yc s ptr.toNat (xl.toNat + 4) _ _ m
      (mid_of_alloc hpre hyx hra hx15 hdf ?hG ?_ ?_ ?_ ?_ ?_ ?_ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp only <;> omega) hLF hMF hAp hIn hle
        (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega)))
        hinv' (by omega) (by omega) hrb (by omega))
      hyx hy0 hxc (by omega)
      ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hG (hWo _ _ (by omega))))
      ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
        (natVal_frame ?hG (hWo _ _ (by omega))))
      ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hG (hWo _ _ (by omega)))) hge
      _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hG => simp only [win]; janus_frame
    all_goals janus64_simp


end FvModexp.Amd64.NatSub
