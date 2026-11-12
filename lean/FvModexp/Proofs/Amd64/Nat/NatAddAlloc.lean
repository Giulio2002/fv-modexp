import FvModexp.Proofs.Amd64.Nat.NatAddReuse

/-! # `nat.add` (amd64): the entry → `makeslice(Word, m + 1, m + 5)` → `+0xe6` (`0 < n ≤ m`, `zc < m + 1`), then `vv` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatAdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibNatAdd.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hz : zc.toNat < xl.toNat + 1) (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatAdd.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostX 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, hyacc, hy48, hyh, hyw, hinv, hok, -⟩ := hpre'
  have hneed : need xl yl = xl.toNat + 1 := by unfold need mx; rw [if_neg (by omega)]; omega
  rw [hneed] at hok
  obtain ⟨hok1, hcost⟩ := hok (by omega)
  rw [show makeCap (xl.toNat + 1) = xl.toNat + 5 by unfold makeCap; rw [if_neg (by omega)]] at hok1
  have hmc : makeCost (xl.toNat + 1) = allocCost (8 * (xl.toNat + 5)) := by
    unfold makeCost makeCap; rw [if_neg (by omega)]
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + 5)) true
  have hbs : blockSize (8 * (xl.toNat + 5)) true ≤ b := by omega
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4288) (4288 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  janus64_run [BitVec.msb_eq_decide, mod64_of_lt (xl.toNat + 1) (by omega), mod64_of_lt (xl.toNat + 5) (by omega),
    toInt_small (xl + 1#64) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] until [hMid] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
  have hWo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n
      [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  refine vv impl hap R hmv b L zp zc xp xl xc yp yl yc s ptr.toNat (xl.toNat + 5) _ _ m
    (mid_of_alloc hpre hyx hra hx15 hdf hz ?hF ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega) hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega)))
      hinv' hrb (by omega))
    hyx hy0 hxc (by omega)
    ((held_keep (hxh.sub (Nat.le_refl _) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
      (natVal_frame ?hF (hWo _ _ (by omega))))
    ((held_keep (hxh.sub (by omega) (by omega)) hLF hMF (hCo _ _ (by omega))).trans
      (natVal_frame ?hF (hWo _ _ (by omega))))
    ((held_keep hyh hLF hMF (hCo _ _ (by omega))).trans (natVal_frame ?hF (hWo _ _ (by omega))))
    _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals janus64_simp

end FvModexp.Amd64.NatAdd
