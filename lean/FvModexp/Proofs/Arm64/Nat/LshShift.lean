import FvModexp.Proofs.Arm64.Nat.LshShiftC

/-!
# `nat.lsh` (arm64): the `s % 64 ≠ 0` path from the join (`+0x16c`) to the clear point

Spills `SP - 24 = p`, `SP - 80 = c`, `SP - 32 = s/64`; `CBNZ R9` (taken); `z[n] = lshVU(z[n-m:n], x, s%64)`:
frame arguments `8 … 56(RSP')` = `(p + 8 (s/64), m, c - s/64, x, m, cap x, s % 64)`, `CALL lshVU.abi0` (`+0x204`),
result `64(RSP') = SP - 96`; reloads; `z[n] = carry`; to `hClr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem shiftA (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0) (hxc : xc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh) (h7 : S.regs 7 = BitVec.ofNat 64 (xl + sh / 64))
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hxl0 := h.xl0; have hal := h.al; have hsacc := h.sacc
  simp only [need] at hcap hn16 h1
  have hsh : sh < 2 ^ 64 := by omega
  have hq := lsr6 sh hsh
  have hq' := shr6 sh hsh
  have hr := and63 sh hsh
  have hr' : (BitVec.ofNat 64 (sh % 64) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hmk := slice_mask (sh / 64) c (by omega) hc40
  have hpq : (p + 8 * (sh / 64)) % 18446744073709551616 = p + 8 * (sh / 64) := Nat.mod_eq_of_lt (by omega)
  have hwrt := h.wrt
  janus_run [hm, hq, hq', hr, hr', hmk, hpq] until [callLsh]
  refine shiftC impl R hLsh hmc b L zp zc x xl sh s p c L' b' M h hr0 _ ?_ ?_ ?_ ?_ ?_ ?F ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?inv
  case F => janus_frame
  case inv =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 152, s.sp.toNat - 96), (s.sp.toNat - 80, s.sp.toNat - 72),
      (s.sp.toNat - 32, s.sp.toNat - 16)]) (by janus_frame) (fun r hr => ?_) h.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (left; exact hwrt.of_sub (by omega) (by omega))
  all_goals janus_simp
  all_goals exact Nat.mod_eq_of_lt (by have := h.x48; omega)

end FvModexp.Arm64.Lsh
