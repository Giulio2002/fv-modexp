import FvModexp.Proofs.Amd64.Nat.LshShift
import FvModexp.Proofs.Amd64.Nat.LshMid

/-!
# `nat.lsh` (amd64): entry (`0 < s`, `0 < len x`) to the join of `z.make(n + 1)` (`+0x1d1`), then `copyM` / `shiftA` (allocation path, shift)

`TESTQ R9; JNE` (taken) → `+0x141`: `TESTQ SI; JE` (not taken); `q = s >> 6 → e - 40`; `n + 1 → e - 56`; `n → e - 48`;
`CMPQ CX, DX; JGE` reuse (`n + 1 ≤ cap z`); else spill `e + 0x38 = s`, `e + 0x30 = cap x`, `e - 80 = n + 5`,
`makeslice(Word, n + 1, n + 5)` (`+0x198`), reloads.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Lsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainAllocS (impl : List Amd64.Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmk : MakesliceLiveContract64 (LibLsh.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibLsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc sh) (hxc : xc < 2 ^ 64) (hz : zc < need xl sh) (hr0 : sh % 64 ≠ 0) (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hsv, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hn16, -,
    hcost, hinv⟩, hsh0, hxl0⟩ := hpre'
  have hsh : sh < 2 ^ 64 := by omega
  have hq := shr6 sh hsh
  have hn : BitVec.ofNat 64 (sh / 64) + BitVec.ofNat 64 xl = BitVec.ofNat 64 (xl + sh / 64) := by
    rw [add_c _ _ (by omega), Nat.add_comm]
  have hn' := add_c xl (sh / 64) (by omega)
  have hn1' := add_c (xl + sh / 64) 1 (by omega)
  have hn5' := add_c (xl + sh / 64) 5 (by omega)
  have hs0 := ofNat_ne0 sh hsh0 hsh
  have hx0 := ofNat_ne0 xl hxl0 (by omega)
  have hz' : zc < xl + sh / 64 + 1 := hz
  have hm1 : (xl + sh / 64 + 1) % 2 ^ 64 = xl + sh / 64 + 1 := Nat.mod_eq_of_lt (by omega)
  have hm5 : (xl + sh / 64 + 5) % 2 ^ 64 = xl + sh / 64 + 5 := Nat.mod_eq_of_lt (by omega)
  have hmz : zc % 2 ^ 64 = zc := Nat.mod_eq_of_lt (by omega)
  have hk1 : need xl sh ≠ 1 := by simp only [need]; omega
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4248) (4248 + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, xl + sh / 64 + 1, xl + sh / 64 + 5] :=
    hsv.1 _ _ _ (by omega)
  have hmcost : makeCost (need xl sh) = allocCost (8 * (xl + sh / 64 + 1 + 4)) := by
    unfold makeCost makeCap; rw [if_neg hk1]
  rw [hmcost] at hcost
  have hbl := blockSize_le_allocCost (8 * (xl + sh / 64 + 1 + 4)) true
  have hbs : blockSize (8 * (xl + sh / 64 + 1 + 4)) true ≤ b := by omega
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  have hcs : ∀ r ∈ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
      ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)],
      (s.regs 4).toNat - 4248 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 56 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  janus64_run [hq, hn, hn', hn1', hn5', hs0, hx0, hm1, hm5, hmz, BitVec.msb_eq_decide] until [hJoin]
    calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
  have hmid := fun hF r1 r2 r3 r4 r5 => mid_of_alloc (round := _) hpre hz hra hx15 hdf hF r1 r2 r3 r4 r5 hcs hLF
    hMF hAp hIn hle (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
    (h8 (Or.inr (by omega))) hinv' (by simp only [need]; omega) (by rw [hmcost]; omega)
  refine shiftA impl R hLsh hmc b L zp zc x xl xc sh s ptr.toNat (need xl sh + 4) _ _ m
    (hmid ?hF ?_ ?_ ?_ ?_ ?_) hr0 hxc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hdf | skip
  all_goals (apply BitVec.eq_of_toNat_eq; simp)

end FvModexp.Amd64.Lsh
