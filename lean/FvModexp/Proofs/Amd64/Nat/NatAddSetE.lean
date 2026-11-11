import FvModexp.Proofs.Amd64.Nat.NatAddSet
import FvModexp.Proofs.Amd64.Nat.NatAddReuse

/-! # `nat.add` (amd64): the entry → `+0x252` on the `z.set(x)` path (`n = 0 < m`), then `setTail` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatAdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setPath (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibNatAdd.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibNatAdd.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatAdd.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hty, hxc, -, hxc40, -, hx40, hy40,
    hz40, -, -, -, hxacc, hx48, hxh, -, -, hxw, -, -, -, -, hinv, hok, -⟩ := hpre'
  have hneed : need xl yl = xl.toNat := by unfold need mx; rw [if_pos (by omega)]; omega
  rw [hneed] at hok
  have hyl : yl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hy0)
  subst hyl
  by_cases hz : xl.toNat ≤ zc.toNat
  · clear hok
    janus64_run [BitVec.msb_eq_decide] until [hSet]
    refine setTail impl R hmv b L zp zc xp xl yp 0#64 s zp.toNat zc.toNat L b _
      (setmid_of_reuse hpre hy0 hx0 hra hx15 hdf hz ?hF ?_ ?_) hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals janus64_simp
  · obtain ⟨hok1, hcost⟩ := hok (by omega)
    clear hok
    have hwt : Apart wordT 16 ((s.regs 4).toNat - 4288) (4288 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
    unfold Apart at hwt hga
    janus64_data hd
    janus_eval_nat h_t : wordT
    rw [h_t] at hty hok1 hwt
    simp only [LiveSep, win] at hLs
    simp only [win, outside_cons, outside_nil, and_true] at hxw
    have hcs : ∀ r ∈ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)],
        (s.regs 4).toNat - 4288 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40 := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    by_cases h1x : xl.toNat = 1
    · have hx1 : xl = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1x)
      subst hx1
      rw [show makeCap (1#64 : BitVec 64).toNat = 1 by decide] at hok1
      have hbl := blockSize_le_allocCost (8 * 1) true
      have hbs : blockSize (8 * 1) true ≤ b := by
        rw [show makeCost (1#64 : BitVec 64).toNat = allocCost (8 * 1) by decide] at hcost; omega
      janus64_run [BitVec.msb_eq_decide] until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
      refine setTail impl R hmv b L zp zc xp 1#64 yp 0#64 s ptr.toNat 1 _ _ m
        (setmid_of_alloc hpre hy0 hx0 hra hx15 hdf (by omega) ?hF ?_ ?_ hcs hLF hMF hAp hIn (by omega)
          (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) h8 hinv'
          (by decide) (by decide) (by decide) (by decide))
        hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [win]; janus_frame
      all_goals janus64_simp
    · rw [show makeCap xl.toNat = xl.toNat + 4 by unfold makeCap; rw [if_neg h1x]] at hok1
      have hmc : makeCost xl.toNat = allocCost (8 * (xl.toNat + 4)) := by
        unfold makeCost makeCap; rw [if_neg h1x]
      have hbl := blockSize_le_allocCost (8 * (xl.toNat + 4)) true
      have hbs : blockSize (8 * (xl.toNat + 4)) true ≤ b := by omega
      janus64_run [BitVec.msb_eq_decide, FvModexp.mod64_of_lt (xl.toNat + 4) (by omega)] until [hSet] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
      refine setTail impl R hmv b L zp zc xp xl yp 0#64 s ptr.toNat (xl.toNat + 4) _ _ m
        (setmid_of_alloc hpre hy0 hx0 hra hx15 hdf (by omega) ?hF ?_ ?_ hcs hLF hMF hAp hIn hle
          (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega)))
          hinv' (by omega) (by omega) hrb (by omega))
        hy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      case hF => simp only [win]; janus_frame
      all_goals janus64_simp

end FvModexp.Amd64.NatAdd
