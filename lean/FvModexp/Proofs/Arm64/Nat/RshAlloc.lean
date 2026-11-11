import FvModexp.Proofs.Arm64.Nat.RshMain

/-! # `nat.rsh` (arm64): entry to the join on the allocation path (`cap z < n`), then copy / shift -/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

/-- the join after either `makeslice`, then copy or shift -/
theorem fromJoin (impl : List Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (hmv : MemmoveLive (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh) (h7 : S.regs 7 = BitVec.ofNat 64 (need xl sh))
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  by_cases hr0 : sh % 64 = 0
  · exact copyM impl R hmv b L zp zc x xl xc sh s p c L' b' M h hr0 hxc hxc' S hpc h0 h1 h2 h3 h4 h5 h6 h7 hsp h28
      h29 h18 hm
  · exact shiftA impl R hRsh b L zp zc x xl xc sh s p c L' b' M h hr0 hxc hxc' S hpc h0 h1 h2 h3 h4 h5 h6 h7 hsp h28
      h29 h18 hm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainAlloc (impl : List Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (hmk : MakesliceLiveContract (LibRsh.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 sh)
    (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40) (hsh0 : 0 < sh) (hn0 : 0 < need xl sh) (hz : zc < need xl sh)
    (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, -, -, -, -, hcost, hinv⟩ := hpre'
  have hn0' : sh / 64 < xl := by simp only [need] at hn0; omega
  have hz' : zc < xl - sh / 64 := hz
  have hsh : sh < 2 ^ 64 := by omega
  have hq := Lsh.lsr6 sh hsh
  have hq' := Lsh.shr6 sh hsh
  have hs := sub_q xl sh hn0' (by omega)
  have hs0 : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 4240) (4240 + 64) := apart_of_data hd 1 (by decide) (by decide) hwa
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hwt
  simp only [LiveSep, win] at hLs
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4240 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  by_cases hk1 : xl - sh / 64 = 1
  · have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by omega)
    rw [h_t] at hok1
    have hmc : makeCost (need xl sh) = allocCost (8 * 1) := by
      simp only [need]; rw [hk1]; decide
    have hbl := blockSize_le_allocCost (8 * 1) true
    have hbs : blockSize (8 * 1) true ≤ b := by omega
    have hn1 : BitVec.ofNat 64 (xl - sh / 64) = 1#64 := by rw [hk1]
    rw [hn1] at hs
    janus_run [hq, hq', hs, hs0] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := 1) hpre hz hn0 (by simp only [need]; omega)
      (by simp only [need]; omega) hl4 hl48 hF r1 r2 hLF hMF hAp hIn (by omega)
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) h8 hinv' (by omega)
      (by rw [hmc]; exact Nat.le_trans (by decide) hbl)
    refine fromJoin impl R hRsh hmv b L zp zc x xl xc sh s ptr.toNat 1 _ _ m (hmid ?hF ?_ ?_) hxc hxc' _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals try janus_simp
    all_goals try (simp only [need]; omega)
    all_goals try omega
    all_goals try (apply BitVec.eq_of_toNat_eq; simp)
    all_goals (simp only [need]; omega)
  · have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl - sh / 64, xl - sh / 64 + 4] := hsv.1 _ _ _ (by omega)
    rw [h_t] at hok1
    have hmc : makeCost (need xl sh) = allocCost (8 * (xl - sh / 64 + 4)) := by
      unfold makeCost makeCap; simp only [need]; rw [if_neg hk1]
    have hbl := blockSize_le_allocCost (8 * (xl - sh / 64 + 4)) true
    have hbs : blockSize (8 * (xl - sh / 64 + 4)) true ≤ b := by omega
    have hk1' : (BitVec.ofNat 64 (xl - sh / 64) = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have h4' : BitVec.ofNat 64 (xl - sh / 64) + 4#64 = BitVec.ofNat 64 (xl - sh / 64 + 4) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    janus_run [hq, hq', hs, hs0, hk1', h4'] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 => mid_of_alloc (c := xl - sh / 64 + 4) hpre hz hn0 (by simp only [need]; omega)
      (by simp only [need]; omega) hl4 hl48 hF r1 r2 hLF hMF hAp hIn hle
      (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc) (h8 (Or.inr (by omega))) hinv'
      hrb (by rw [hmc]; omega)
    refine fromJoin impl R hRsh hmv b L zp zc x xl xc sh s ptr.toNat (xl - sh / 64 + 4) _ _ m (hmid ?hF ?_ ?_) hxc
      hxc' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Arm64.Rsh
