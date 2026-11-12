import FvModexp.Proofs.Amd64.Nat.RshShift
import FvModexp.Proofs.Amd64.Nat.RshMid

/-!
# `nat.rsh` (amd64): entry to the join of `z.make(n)` on the allocation path (`cap z < n`), `n = 1` (`make(nat, 1, 1)`), then
`copyM` / `shiftA`

Spills `e - 40 = s`, `e - 48 = n`, `e + 0x30 = cap x`; `makeslice(Word, 1, 1)` (`+0x18c`); reloads; join.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainAlloc1S (impl : List Amd64.Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (hmk : MakesliceLiveContract64 (LibRsh.program.link impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc sh) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40) (hsh : sh < 2 ^ 64) (hs0 : 0 < sh)
    (hn0 : 0 < need xl sh) (hz : zc < need xl sh) (hn1 : need xl sh = 1) (hr0 : sh % 64 ≠ 0)
    (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, hgr, hLs, hro, ⟨-, htr, htw⟩⟩, hsv, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, -,
    -, -, -, hcost, hinv⟩ := hpre'
  have hq := shr6 sh hsh
  have hxn : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xl - sh / 64) := by
    simp only [need] at hn0
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs0' := ofNat_ne0 sh hs0 hsh
  have hmz : zc % 2 ^ 64 = zc := Nat.mod_eq_of_lt (by omega)
  have hmn : (xl - sh / 64) % 2 ^ 64 = xl - sh / 64 := Nat.mod_eq_of_lt (by omega)
  have hz' : zc < xl - sh / 64 := hz
  have hn0' : 0 < xl - sh / 64 := hn0
  have hn1' : xl - sh / 64 = 1 := hn1
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4248) (4248 + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by omega)
  have hmcost : makeCost (need xl sh) = allocCost (8 * 1) := by rw [hn1]; try decide
  have hn1v : BitVec.ofNat 64 (xl - sh / 64) = 1#64 := by rw [hn1']
  rw [hmcost] at hcost
  have hbl := blockSize_le_allocCost (8 * (1)) true
  have hbs : blockSize (8 * (1)) true ≤ b := by omega
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
  janus64_run [hq, hxn, hs0', hmz, hmn, hn1v, BitVec.msb_eq_decide] until [hJoin] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _ _
  have hmid := fun hF r1 r2 => mid_of_alloc (round := _) hpre hz hra hx15 hdf hF r1 r2 hn0 hcs hLF
    hMF hAp hIn (by omega) (by rw [hMF.accessible]; simpa only [Janus.Arm64.Memory.accessible_writeLE] using hacc)
    h8 hinv' (c := 1) (by omega) (by decide) (by omega) (by rw [hmcost]; decide)
  refine shiftA impl R hRsh b L zp zc x xl xc sh s ptr.toNat _ _ _ m
    (hmid ?hF ?_ ?_) hr0 hxc hxc' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hdf | skip
  all_goals (apply BitVec.eq_of_toNat_eq; simp)
  all_goals (simp only [need] at hn1 ⊢; omega)

end FvModexp.Amd64.Rsh
