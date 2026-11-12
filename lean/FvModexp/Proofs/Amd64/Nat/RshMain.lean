import FvModexp.Proofs.Amd64.Nat.RshShift
import FvModexp.Proofs.Amd64.Nat.RshCopy
import FvModexp.Proofs.Amd64.Nat.RshMid

/-!
# `nat.rsh` (amd64): entry (`0 < s`, `s/64 < len x`) to the join of `z.make(n)` (`+0x1fe`) on the reuse path
(`n ≤ cap z`), then `copyM` / `shiftA`

`TESTQ R9; JNE` (taken) → `+0x141`: `DX = s`, `R9 = s >> 6`, `BX = m - R9` (`n`), `TESTQ BX; JLE` (not taken),
`CMPQ CX, BX; JL` (not taken), `R9 = n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainReuse (impl : List Amd64.Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (hmv : MemmoveLive64 (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc sh) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40) (hsh : sh < 2 ^ 64) (hs0 : 0 < sh)
    (hn0 : 0 < need xl sh) (hz : need xl sh ≤ zc) (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨-, -, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, -⟩ := hpre'
  have hq := shr6 sh hsh
  have hxn : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xl - sh / 64) := by
    simp only [need] at hn0
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs0' := ofNat_ne0 sh hs0 hsh
  have hmz : zc % 2 ^ 64 = zc := Nat.mod_eq_of_lt (by omega)
  have hmn : (xl - sh / 64) % 2 ^ 64 = xl - sh / 64 := Nat.mod_eq_of_lt (by omega)
  have hz' : xl - sh / 64 ≤ zc := hz
  have hn0' : 0 < xl - sh / 64 := hn0
  by_cases hr0 : sh % 64 = 0
  · janus64_run [hq, hxn, hs0', hmz, hmn, BitVec.msb_eq_decide] until [hJoin]
    refine copyM impl R hmv b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hra hx15 hdf ?hF ?_ ?_ hn0) hr0 hxc hxc' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
  · janus64_run [hq, hxn, hs0', hmz, hmn, BitVec.msb_eq_decide] until [hJoin]
    refine shiftA impl R hRsh b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hra hx15 hdf ?hF ?_ ?_ hn0) hr0 hxc hxc' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Rsh
