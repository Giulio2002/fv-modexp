import FvModexp.Proofs.Arm64.Nat.RshShift
import FvModexp.Proofs.Arm64.Nat.RshCopy
import FvModexp.Proofs.Arm64.Nat.RshMid

/-!
# `nat.rsh` (arm64): entry (`0 < s`, `0 < n = len x - s/64`) to the join of `z.make(n)` (`+0x1ac`), then copy / shift

`CBNZ R6` (taken) → `+0x118`: `n = m - s/64`; `CMP $0, R1; BLE` (not taken); `CMP R1, R2; BGT` → allocate (spills
`SP + 56 = s`, `SP - 32 = n`, `SP + 48 = cap x`; `n = 1`: `makeslice(Word, 1, 1)`, else `SP - 64 = n + 4`,
`makeslice(Word, n, n + 4)`; reloads), else reuse.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

theorem sub_q (xl sh : Nat) (h : sh / 64 < xl) (hx : xl < 2 ^ 64) :
    BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xl - sh / 64) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem mainReuse (impl : List Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (hmv : MemmoveLive (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc sh : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 sh)
    (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40) (hsh0 : 0 < sh) (hn0 : 0 < need xl sh) (hz : need xl sh ≤ zc)
    (hpre : Pre R b L zp zl zc x xl sh s) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hx16, -⟩ := hpre'
  have hn0' : sh / 64 < xl := by simp only [need] at hn0; omega
  have hz' : xl - sh / 64 ≤ zc := hz
  have hsh : sh < 2 ^ 64 := by omega
  have hq := Lsh.lsr6 sh hsh
  have hq' := Lsh.shr6 sh hsh
  have hs := sub_q xl sh hn0' (by omega)
  have hs0 : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  by_cases hr0 : sh % 64 = 0
  · janus_run [hq, hq', hs, hs0] until [hJoin]
    refine copyM impl R hmv b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hn0 hl4 hl48 ?hF ?_ ?_) hr0 hxc hxc' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · janus_run [hq, hq', hs, hs0] until [hJoin]
    refine shiftA impl R hRsh b L zp zc x xl xc sh s zp zc L b _
      (mid_of_reuse hpre hz hn0 hl4 hl48 ?hF ?_ ?_) hr0 hxc hxc' _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

end FvModexp.Arm64.Rsh
