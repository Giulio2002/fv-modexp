import FvModexp.Proofs.Amd64.Nat.LshShift
import FvModexp.Proofs.Amd64.Nat.LshCopy
import FvModexp.Proofs.Amd64.Nat.LshMid

/-!
# `nat.lsh` (amd64): entry (`0 < s`, `0 < len x`) to the join of `z.make(n + 1)` (`+0x1d1`), then `copyM` / `shiftA` (reuse path)

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
theorem mainReuse (impl : List Amd64.Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmv : MemmoveLive64 (LibLsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc sh) (hxc : xc < 2 ^ 64) (hz : need xl sh ≤ zc) (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hn16, -, -, -⟩, hsh0, hxl0⟩ := hpre'
  have hsh : sh < 2 ^ 64 := by omega
  have hq := shr6 sh hsh
  have hn : BitVec.ofNat 64 (sh / 64) + BitVec.ofNat 64 xl = BitVec.ofNat 64 (xl + sh / 64) := by
    rw [add_c _ _ (by omega), Nat.add_comm]
  have hn' := add_c xl (sh / 64) (by omega)
  have hn1' := add_c (xl + sh / 64) 1 (by omega)
  have hs0 := ofNat_ne0 sh hsh0 hsh
  have hx0 := ofNat_ne0 xl hxl0 (by omega)
  have hz' : xl + sh / 64 + 1 ≤ zc := hz
  have hm1 : (xl + sh / 64 + 1) % 2 ^ 64 = xl + sh / 64 + 1 := Nat.mod_eq_of_lt (by omega)
  have hmz : zc % 2 ^ 64 = zc := Nat.mod_eq_of_lt (by omega)
  by_cases hr0 : sh % 64 = 0
  · janus64_run [hq, hn, hn', hn1', hs0, hx0, hm1, hmz, BitVec.msb_eq_decide] until [hJoin]
    refine copyM impl R hmv hmc b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hra hx15 hdf ?hF ?_ ?_ ?_ ?_ ?_) hr0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
  · janus64_run [hq, hn, hn', hn1', hs0, hx0, hm1, hmz, BitVec.msb_eq_decide] until [hJoin]
    refine shiftA impl R hLsh hmc b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hra hx15 hdf ?hF ?_ ?_ ?_ ?_ ?_) hr0 hxc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      rfl
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Lsh
