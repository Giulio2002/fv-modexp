import FvModexp.Proofs.Amd64.Nat.RshShiftC

/-!
# `nat.rsh` (amd64): the `s % 64 ≠ 0` path from the join (`+0x1fe`) to `CALL rshVU.abi0` (`+0x2ac`), then `shiftC`

Spills `e - 72 = c`, `e - 80 = n`, `e - 24 = p`; `ANDL $0x3f, DX; TESTQ; JNE` (taken); frame words `p, n, c`; the
slice `x[m-n:]` (`q = m - n`, `cap x - q`, mask, `x + 8q`) and `n`, `cap x - q`, `s % 64`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

theorem and63 (sh : Nat) (hsh : sh < 2 ^ 64) : BitVec.ofNat 64 sh &&& 63#64 = BitVec.ofNat 64 (sh % 64) := by
  have e : sh &&& 63 = sh % 64 := Nat.and_two_pow_sub_one_eq_mod sh 6
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, e]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem shiftA (impl : List Amd64.Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h3 : S.regs 3 = BitVec.ofNat 64 (need xl sh))
    (h2 : S.regs 2 = BitVec.ofNat 64 sh) (h6 : S.regs 6 = BitVec.ofNat 64 xl)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 (need xl sh))
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn0 := h.n0; have hal := h.al; have hsacc := h.sacc; have hx48 := h.x48; have hx16 := h.xl16
  simp only [need] at hcap hn0 h3 h9
  have hsh : sh < 2 ^ 64 := by omega
  have hr := and63 sh hsh
  have hr' : (BitVec.ofNat 64 (sh % 64) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hq8 : 8 * (sh / 64) < 2 ^ 64 := by omega
  have hs3 := shl3 (sh / 64) hq8
  have hxq : BitVec.ofNat 64 xl - BitVec.ofNat 64 (xl - sh / 64) = BitVec.ofNat 64 (sh / 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hxn : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xl - sh / 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hcq : BitVec.ofNat 64 xc - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xc - sh / 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmask : ((0#64 - BitVec.ofNat 64 (xc - sh / 64)).sshiftRight 63 &&& BitVec.ofNat 64 (8 * (sh / 64))) =
      BitVec.ofNat 64 (8 * (sh / 64)) :=
    neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hxq1 : BitVec.ofNat 64 (8 * (sh / 64)) + BitVec.ofNat 64 x = BitVec.ofNat 64 (x + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hxq2 : BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * (sh / 64)) = BitVec.ofNat 64 (x + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hwrt := h.wrt
  janus64_run [hm, hfs, hr, hr', hs3, hxq, hxn, hcq, hmask, hxq1, hxq2, BitVec.msb_eq_decide] until [callRsh]
  refine shiftC impl R hRsh b L zp zc x xl sh s p c L' b' M h hr0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?F ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?inv
  case F => janus_frame
  case inv =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 144, (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 64), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)])
      (by janus_frame) (fun r hr => ?_) h.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (left; exact hwrt.of_sub (by omega) (by omega))
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf | skip

end FvModexp.Amd64.Rsh
