import FvModexp.Proofs.Arm64.Nat.LshShift
import FvModexp.Proofs.Arm64.Nat.LshCopy
import FvModexp.Proofs.Arm64.Nat.LshMid

/-!
# `nat.lsh` (arm64): entry (`0 < s`, `0 < len x`) to the join of `z.make(n + 1)` (`+0x16c`), then `copyM` / `shiftA`

`CBNZ R6` (taken) → `+0x118`: `CBZ R4` (not taken); spill `SP + 56 = s`; `n = m + s/64` → `SP - 40`; `n + 1` → `SP - 48`;
`CMP R1, R2; BGE` reuse (`n + 1 ≤ cap z`); else spill `SP + 48 = cap x`, `SP - 80 = n + 5`,
`makeslice(Word, n + 1, n + 5)`, reloads.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh

theorem add_n (xl sh : Nat) (h : xl + sh / 64 + 1 ≤ 2 ^ 16) :
    BitVec.ofNat 64 xl + BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xl + sh / 64) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem add_c (v k : Nat) (h : v + k < 2 ^ 64) :
    BitVec.ofNat 64 v + BitVec.ofNat 64 k = BitVec.ofNat 64 (v + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainReuse (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmv : MemmoveLive (LibLsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 sh)
    (hxc : xc < 2 ^ 64) (hz : need xl sh ≤ zc) (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hn16, -, -, -⟩, hsh0, hxl0⟩ := hpre'
  have hsh : sh < 2 ^ 64 := by omega
  have hq := lsr6 sh hsh
  have hq' := shr6 sh hsh
  have hn := add_n xl sh hn16
  have hn1 := add_c (xl + sh / 64) 1 (by omega)
  have hs0 : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hx0 : (BitVec.ofNat 64 xl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hz' : xl + sh / 64 + 1 ≤ zc := hz
  by_cases hr0 : sh % 64 = 0
  · janus_run [hq, hq', hn, hn1, hs0, hx0] until [hJoin]
    refine copyM impl R hmv hmc b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hl4 hl48 ?hF ?_ ?_ ?_ ?_ ?_) hr0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · janus_run [hq, hq', hn, hn1, hs0, hx0] until [hJoin]
    refine shiftA impl R hLsh hmc b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hl4 hl48 ?hF ?_ ?_ ?_ ?_ ?_) hr0 hxc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainAlloc (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmk : MakesliceLiveContract (LibLsh.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (LibLsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 sh)
    (hxc : xc < 2 ^ 64) (hz : zc < need xl sh) (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hn16, -, hcost, hinv⟩, hsh0, hxl0⟩ := hpre'
  have hsh : sh < 2 ^ 64 := by omega
  have hq := lsr6 sh hsh
  have hq' := shr6 sh hsh
  have hn := add_n xl sh hn16
  have hn1 := add_c (xl + sh / 64) 1 (by omega)
  have hn5 := add_c (xl + sh / 64) 5 (by omega)
  have hs0 : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hx0 : (BitVec.ofNat 64 xl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hk1 : need xl sh ≠ 1 := by simp only [need]; omega
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 4256) (4256 + 64) := apart_of_data hd 1 (by decide) (by decide) hwa
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl + sh / 64 + 1, xl + sh / 64 + 5] :=
    hsv.1 _ _ _ (by omega)
  rw [show makeCost (need xl sh) = allocCost (8 * (xl + sh / 64 + 1 + 4)) by
    unfold makeCost makeCap; rw [if_neg hk1]] at hcost
  have hbl := blockSize_le_allocCost (8 * (xl + sh / 64 + 1 + 4)) true
  have hbs : blockSize (8 * (xl + sh / 64 + 1 + 4)) true ≤ b := by omega
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  have hWo : ∀ a n, (a + n ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4256 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hmcost : makeCost (need xl sh) = allocCost (8 * (xl + sh / 64 + 1 + 4)) := by
    unfold makeCost makeCap; rw [if_neg hk1]
  have hz' : zc < xl + sh / 64 + 1 := hz
  by_cases hr0 : sh % 64 = 0
  · janus_run [hq, hq', hn, hn1, hn5, hs0, hx0] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 r3 r4 r5 => mid_of_alloc (round := _) hpre hz hl4 hl48 hF r1 r2 r3 r4 r5 hLF hMF hAp
      hIn hle (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by simp only [need]; omega) (by rw [hmcost]; omega)
    refine copyM impl R hmv hmc b L zp zc x xl xc sh s ptr.toNat (need xl sh + 4) _ _ m
      (hmid ?hF ?_ ?_ ?_ ?_ ?_) hr0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp)
  · janus_run [hq, hq', hn, hn1, hn5, hs0, hx0] until [hJoin] calls [hmk.pos]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    have hmid := fun hF r1 r2 r3 r4 r5 => mid_of_alloc (round := _) hpre hz hl4 hl48 hF r1 r2 r3 r4 r5 hLF hMF hAp
      hIn hle (by rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc)
      (h8 (Or.inr (by omega))) hinv' (by simp only [need]; omega) (by rw [hmcost]; omega)
    refine shiftA impl R hLsh hmc b L zp zc x xl xc sh s ptr.toNat (need xl sh + 4) _ _ m
      (hmid ?hF ?_ ?_ ?_ ?_ ?_) hr0 hxc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
    all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Arm64.Lsh
